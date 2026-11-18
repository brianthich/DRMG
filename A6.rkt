#lang typed/racket

(require typed/rackunit)

;; Progress: Required DRMG6 features implemented, including :=, rocal,
;; while, and in-order. Optional quicksort is not included.

(define-type ExprC (U NumC BoolC StrC IdC IfC LamC AppC SetC RecC))
(struct NumC ([n : Real]) #:transparent)
(struct BoolC ([b : Boolean]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct IdC ([name : Symbol]) #:transparent)
(struct IfC ([test : ExprC] [yes : ExprC] [no : ExprC]) #:transparent)
(struct LamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct SetC ([name : Symbol] [rhs : ExprC]) #:transparent)
(struct RecC ([name : Symbol] [rhs : ExprC] [body : ExprC]) #:transparent)

(define-type Value (U NumV BoolV StrV ClosureV PrimV ArrayV NullV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct ClosureV ([params : (Listof Symbol)] [body : ExprC] [env : Environment]) #:transparent)
(struct PrimV ([name : Symbol]) #:transparent)
(struct Binding ([name : Symbol] [loc : Natural]) #:transparent)
(define-type Environment (Listof Binding))
(struct ArrayV ([base : Natural] [size : Natural]) #:transparent)
(struct NullV () #:transparent)

(define-type Store (Vectorof (U Natural Value)))

;; Reserved syntax words cannot be used as identifiers; primitive names can.
(define reserved (set 'if '= 'local 'rocal '% '-> 'in))

;; Returns n as a natural number, or false if it is inexact, fractional, or negative.
(: natural-index (-> Real (U Natural False)))
(define (natural-index n)
  (if (and (integer? n) (exact? n) (<= 0 n)) n #f))

;; Reads a stored DRMG value; the raw allocation pointer is not a DRMG value.
(: read-store (-> Store Natural Value))
(define (read-store sto loc)
  (define v (vector-ref sto loc))
  (if (real? v)
      (error 'DRMG "cannot read allocation pointer as a value at location ~a" loc)
      v))

;; Creates a store containing the top-level bindings and allocation pointer.
(: make-initial-store (-> Natural Store))
(define (make-initial-store memsize)
  (define checked-size
    (if (< memsize (+ 1 (length top-env)))
        (error 'DRMG "out of memory: need at least ~a cells, received ~a"
               (+ 1 (length top-env)) memsize)
        memsize))
  (define blank : (U Natural Value) (NumV 0))
  (define sto : Store (make-vector checked-size blank))
  (vector-set! sto 0 (+ 1 (length top-env)))
  (for ([b top-env])
    (match b
      [(Binding 'true loc) (vector-set! sto loc (BoolV #t))]
      [(Binding 'false loc) (vector-set! sto loc (BoolV #f))]
      [(Binding name loc) (vector-set! sto loc (PrimV name))]))
  sto)

;; Reserves count consecutive store cells and returns their starting location.
(: allocate (-> Store Natural Natural))
(define (allocate sto count)
  (define next (vector-ref sto 0))
  (if (real? next)
      (if (<= (+ next count) (vector-length sto))
          (begin
            (vector-set! sto 0 (+ next count))
            next)
          (error 'DRMG "out of memory allocating ~a cells in store of size ~a"
                 count (vector-length sto)))
      (error 'DRMG "invalid store allocation pointer: ~e" next)))

;; Returns true if the supplied list contains a reserved syntax word.
(define (check-invalid-symbols [lst : (Listof Any)]) : Boolean
  (match lst
    [(cons f r)
     (if (set-member? reserved f) #t (check-invalid-symbols r))]
    ['() #f]))

;; Returns the store location associated with an identifier.
(: lookup (-> Symbol Environment Natural))
(define (lookup name env)
  (match env
    ['() (error 'DRMG "unbound identifier: ~e" name)]
    [(cons (Binding n loc) rest)
     (if (equal? n name)
         loc
         (lookup name rest))]))

;; Allocates locations for parameters and extends the environment.
(define (extend-env [params : (Listof Symbol)]
                    [values : (Listof Value)]
                    [env : Environment]
                    [sto : Store]) : Environment
  (match* (params values)
    [('() '()) env]
    [((cons p ps) (cons v vs))
     (define loc (allocate sto 1))
     (vector-set! sto loc v)
     (cons (Binding p loc) (extend-env ps vs env sto))]
    [(_ _)
     (error 'DRMG "wrong arity: parameters ~e, values ~e"
            params values)]))

;; Parses DRMG6 syntax into its expression representation.
(: parse (-> Sexp ExprC))
(define (parse s)
  (parse-expr s))

;; Validates and parses a value from a match pattern; malformed syntax raises DRMG.
;; Nested repeated patterns may infer Any, so this helper checks the syntax itself.
(: parse-expr (-> Any ExprC))
(define (parse-expr s)
  (match s
    [(? real? n) (NumC n)]
    [(? string? str) (StrC str)]
    [(? symbol? id)
     (if (check-invalid-symbols (list id))
         (error 'DRMG "reserved word used as identifier in ~e" s)
         (IdC id))]
    [(list 'if tst yes no)
     (IfC (parse-expr tst) (parse-expr yes) (parse-expr no))]
    [(list '% params ... '-> body)
     (define ps : (Listof Symbol)
       (for/list : (Listof Symbol) ([p params])
         (if (symbol? p)
             p
             (error 'DRMG "function parameter must be a symbol in ~e" s))))
     (if (check-duplicates ps)
         (error 'DRMG "duplicate function parameter in ~e" s)
         (if (check-invalid-symbols ps)
             (error 'DRMG "reserved function parameter in ~e" s)
             (LamC ps (parse-expr body))))]
    [(list 'local bindings ... 'in body)
     (define pairs : (Listof (Pairof Symbol ExprC))
       (for/list : (Listof (Pairof Symbol ExprC)) ([b bindings])
         (match b
           [(list (? symbol? name) '= rhs)
            (if (check-invalid-symbols (list name))
                (error 'DRMG "reserved local name in ~e" s)
                (cons name (parse-expr rhs)))]
           [_ (error 'DRMG "malformed local binding in ~e" b)])))
     (define names
       (for/list : (Listof Symbol) ([pair pairs])
         (match pair [(cons name rhs) name])))
     ;; The binding values are already parsed; desugar directly into the AST.
     (if (check-duplicates names)
         (error 'DRMG "duplicate local name in ~e" s)
         (AppC (LamC names (parse-expr body))
               (for/list : (Listof ExprC) ([pair pairs])
                 (match pair [(cons name rhs) rhs]))))]
    [(list (? symbol? name) ':= rhs)
     (if (check-invalid-symbols (list name))
         (error 'DRMG "reserved assignment target in ~e" s)
         (SetC name (parse-expr rhs)))]
    [(list _ ':= _ ...)
     (error 'DRMG "assignment requires a name and one expression in ~e" s)]
    [(list 'rocal (list (? symbol? name) '= rhs) 'in body)
     (if (check-invalid-symbols (list name))
         (error 'DRMG "reserved recursive binding name in ~e" s)
         (RecC name (parse-expr rhs) (parse-expr body)))]
    [(list 'rocal _ ...)
     (error 'DRMG "rocal requires one [name = expression] binding and a body in ~e" s)]
    [(list f args ...)
     (AppC (parse-expr f)
           (for/list : (Listof ExprC) ([arg args])
             (parse-expr arg)))]
    [_ (error 'DRMG "invalid syntax in ~e" s)]))

;; Escapes the remaining string characters and appends the closing quotation mark.
;; string-append is needed to assemble the quoted result without format or ~v.
(: quote-string-rest (-> String Natural String))
(define (quote-string-rest s pos)
  (if (= pos (string-length s))
      "\""
      (string-append
       (match (substring s pos (+ pos 1))
         ["\"" "\\\""]
         ["\\" "\\\\"]
         ["\n" "\\n"]
         ["\r" "\\r"]
         ["\t" "\\t"]
         ["\a" "\\a"]
         ["\b" "\\b"]
         ["\v" "\\v"]
         ["\f" "\\f"]
         [other other])
       (quote-string-rest s (+ pos 1)))))

;; Serializes a DRMG value into its string representation.
(: serialize (-> Value String))
(define (serialize v)
  (match v
    [(NumV n) (number->string n)]
    [(BoolV #t) "true"]
    [(BoolV #f) "false"]
    [(StrV s) (string-append "\"" (quote-string-rest s 0))]
    [(ClosureV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]
    [(ArrayV _ _) "#<array>"]
    [(NullV) "null"]))


;; Retrieves a number from a value or raises a helpful DRMG error.
(: expect-num (-> Value Symbol ExprC Real))
(define (expect-num v op whole)
  (match v [(NumV n) n] [_ (error 'DRMG "~a expected a number; received ~a in ~e" op (serialize v) whole)]))

;; Applies a primitive operator to already evaluated arguments.
(: apply-prim (-> Symbol (Listof Value) ExprC Store Value))
(define (apply-prim op vs whole sto)
  (match* (op vs)
    [((or '+ '- '* '/ '<=) (list left right))
     (define a (expect-num left op whole))
     (define b (expect-num right op whole))
     (match op
       ['+ (NumV (+ a b))]
       ['- (NumV (- a b))]
       ['* (NumV (* a b))]
       ['/ (if (zero? b)
               (error 'DRMG "division by zero in ~e" whole)
               (NumV (/ a b)))]
       [_ (BoolV (<= a b))])]
    [('strlen (list (StrV s))) (NumV (string-length s))]
    [('strlen (list _))
     (error 'DRMG "strlen expected a string in ~e" whole)]
    [('substring (list (StrV s) (NumV start) (NumV stop)))
     (define a (natural-index start))
     (define b (natural-index stop))
     (if (and a b (<= a b) (<= b (string-length s)))
         (StrV (substring s a b))
         (error 'DRMG "substring indices must be natural, in range, and ordered in ~e" whole))]
    [('substring (list _ _ _))
     (error 'DRMG "substring expected a string and two natural indices in ~e" whole)]
    [('equal? (list a b))
     (BoolV (match* (a b)
              [((NumV x) (NumV y)) (= x y)]
              [((BoolV x) (BoolV y)) (equal? x y)]
              [((StrV x) (StrV y)) (equal? x y)]
              [((ArrayV x _) (ArrayV y _)) (= x y)]
              [((NullV) (NullV)) #t]
              [(_ _) #f]))]
    [('make-array (list (NumV size) init))
     (define checked (natural-index size))
     (define count
       (if (and checked (> checked 0))
           checked
           (error 'DRMG "make-array requires a positive integer size in ~e" whole)))
     (define base (allocate sto count))
     (for ([i (in-range count)])
       (vector-set! sto (+ base i) init))
     (ArrayV base count)]
    [('array (cons _ _))
     (define base (allocate sto (length vs)))
     (for ([v vs] [i (in-range (length vs))])
       (vector-set! sto (+ base i) v))
     (ArrayV base (length vs))]
    [('aref (list (ArrayV base size) (NumV index)))
     (define checked (natural-index index))
     (if (and checked (< checked size))
         (read-store sto (+ base checked))
         (error 'DRMG "aref index ~e out of bounds for array of size ~a in ~e"
                index size whole))]
    [('aset! (list (ArrayV base size) (NumV index) val))
     (define checked (natural-index index))
     (if (and checked (< checked size))
         (begin
           (vector-set! sto (+ base checked) val)
           (NullV))
         (error 'DRMG "aset! index ~e out of bounds for array of size ~a in ~e"
                index size whole))]
    [('array '())
     (error 'DRMG "array requires at least one element in ~e" whole)]
    [('make-array (list _ _))
     (error 'DRMG "make-array requires a positive integer size in ~e" whole)]
    [('aref (list _ _))
     (error 'DRMG "aref requires an array and a numeric index in ~e" whole)]
    [('aset! (list _ _ _))
     (error 'DRMG "aset! requires an array, a numeric index, and a value in ~e" whole)]
    [('error (list v))
     (error 'DRMG "user-error ~a in ~e" (serialize v) whole)]
    [((or '+ '- '* '/ '<= 'strlen 'substring 'equal?
          'error 'make-array 'aref 'aset!) _)
     (error 'DRMG "wrong arity for ~a: received ~a arguments in ~e"
            op (length vs) whole)]
    [(_ _)
     (error 'DRMG "unknown primitive ~e in ~e" op whole)]))

;; Evaluates an expression in an environment and shared store.
(: interp (-> ExprC Environment Store Value))
(define (interp e env sto)
  (match e
    [(NumC n) (NumV n)]
    [(BoolC b) (BoolV b)]
    [(StrC s) (StrV s)]
    [(IdC name) (read-store sto (lookup name env))]
    [(IfC tst yes no)
     (match (interp tst env sto)
       [(BoolV #t) (interp yes env sto)]
       [(BoolV #f) (interp no env sto)]
       [v (error 'DRMG "if test must be boolean; received ~a in ~e" (serialize v) e)])]
    [(LamC ps body) (ClosureV ps body env)]
    [(SetC name rhs)
     (define loc (lookup name env))
     (define v (interp rhs env sto))
     (vector-set! sto loc v)
     (NullV)]
    [(RecC name rhs body)
     (define loc (allocate sto 1))
     (define extended (cons (Binding name loc) env))
     (vector-set! sto loc (NullV))
     (define v (interp rhs extended sto))
     (vector-set! sto loc v)
     (interp body extended sto)]
    [(AppC f args)
     (define fv (interp f env sto))
     (define av
       (for/list : (Listof Value) ([arg args])
         (interp arg env sto)))
     (match fv
       [(ClosureV ps body saved)
        (if (= (length ps) (length av))
            (interp body (extend-env ps av saved sto) sto)
            (error 'DRMG "wrong arity: function expected ~a arguments, received ~a in ~e"
                   (length ps) (length av) e))]
       [(PrimV op) (apply-prim op av e sto)]
       [_ (error 'DRMG "attempted to call a non-function value in ~e" e)])]))

;; Associates top-level names with reserved store locations.
(: top-env Environment)
(define top-env
  (for/list : Environment
    ([n '(true false + - * / <= substring strlen equal? error
               make-array array aref aset!)]
     [i (in-range 1 16)])
    (define loc (natural-index i))
    (if loc
        (Binding n loc)
        (error 'DRMG "invalid top-level store location: ~e" i))))

;; Parses and evaluates a program with a fresh store.
(: top-interp (-> Sexp Natural String))
(define (top-interp s memsize)
  (serialize (interp (parse s) top-env (make-initial-store memsize))))

;; DRMG6 function: repeatedly calls body while the zero-argument guard returns true.
;; A local binding sequences each body call before the next recursive call.
(define while : Sexp
  '{rocal [loop = {% guard body ->
                     {if {guard}
                         {local [unused = {body}] in {loop guard body}}
                         false}}]
          in loop})

;; DRMG6 function: checks whether the given array's size elements strictly increase.
;; The surrounding DRMG6 environment must bind while to the expression above.
(define in-order : Sexp
  '{% a size ->
      {local [i = 1] [ordered = true] in
        {local [unused =
                       {while
                        {% -> {if ordered {<= {+ i 1} size} false}}
                        {% -> {if {<= {aref a i} {aref a {- i 1}}}
                                  {ordered := false}
                                  {i := {+ i 1}}}}}]
          in ordered}}})


;; Tests for identifier validation and location-based environments.
(check-equal? (check-invalid-symbols '()) #f)
(check-equal? (check-invalid-symbols '(+ true value)) #f)
(check-equal? (check-invalid-symbols '(x if y)) #t)
(check-equal? (lookup 'x (list (Binding 'x 4))) 4)
(check-equal? (lookup 'x (list (Binding 'x 5) (Binding 'x 7))) 5)
(check-exn #rx"DRMG.*unbound" (lambda () (lookup 'x '())))

(define env-test-sto : Store (make-initial-store 25))
(check-equal?
 (extend-env '(x y) (list (NumV 2) (BoolV #t))
             (list (Binding 'x 5)) env-test-sto)
 (list (Binding 'x 16) (Binding 'y 17) (Binding 'x 5)))
(check-equal? (vector-ref env-test-sto 16) (NumV 2))
(check-equal? (vector-ref env-test-sto 17) (BoolV #t))
(check-equal? (vector-ref env-test-sto 0) 18)
(check-exn #rx"DRMG.*arity"
           (lambda () (extend-env '(x) '() '() (make-initial-store 25))))
(check-exn #rx"DRMG.*arity"
           (lambda () (extend-env '() (list (NumV 2)) '()
                                  (make-initial-store 25))))

;; Tests parser support for literals, application, functions, and local desugaring.
(check-equal? (parse-expr 5) (NumC 5))
(check-exn #rx"DRMG" (lambda () (parse-expr #t)))
(check-equal?
 (parse-expr '(local [x = (+ 1 2)] in x))
 (AppC (LamC '(x) (IdC 'x))
       (list (AppC (IdC '+) (list (NumC 1) (NumC 2))))))
(check-equal? (parse 5) (NumC 5))
(check-equal? (parse "hi") (StrC "hi"))
(check-equal? (parse '(if true 1 2)) (IfC (IdC 'true) (NumC 1) (NumC 2)))
(check-equal? (parse '((% x -> x) 4)) (AppC (LamC '(x) (IdC 'x)) (list (NumC 4))))
(check-equal? (parse '(local [x = 2] [y = 3] in {+ x y}))
              (AppC (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))) (list (NumC 2) (NumC 3))))
(check-exn #rx"DRMG" (lambda () (parse '(% x x -> x))))
(check-exn #rx"DRMG" (lambda () (parse '(if true 1))))
(check-exn #rx"DRMG" (lambda () (parse '(% if -> 1))))
(check-exn #rx"DRMG" (lambda () (parse '(% 3 -> 1))))
(check-exn #rx"DRMG" (lambda () (parse '(local [x = 1] [x = 2] in x))))
(check-exn #rx"DRMG" (lambda () (parse '(local [if = 1] in 2))))
(check-exn #rx"DRMG" (lambda () (parse '(local [x 1] in x))))
(check-exn #rx"DRMG" (lambda () (parse #t)))
(check-exn #rx"DRMG" (lambda () (parse '())))

;; Tests serialization across all value categories.
(check-equal? (serialize (NumV 34)) "34")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (StrV "hi")) "\"hi\"")
(check-equal? (serialize (PrimV '+)) "#<primop>")
(check-equal? (serialize (ClosureV '() (NumC 0) '())) "#<procedure>")

;; Tests top-level programs for primitives, closures, booleans, and strings.
(check-equal? (interp (BoolC #t) top-env (make-initial-store 1000)) (BoolV #t))
(check-equal? (interp (BoolC #f) top-env (make-initial-store 1000)) (BoolV #f))
(check-equal? (top-interp '(+ 1 2) 1000) "3")
(check-equal? (top-interp '(if (<= 2 3) "yes" "no") 1000) "\"yes\"")
(check-equal? (top-interp '((% x -> (* x x)) 5) 1000) "25")
(check-equal? (top-interp '(local [x = 4] [y = 6] in (+ x y)) 1000) "10")
(check-equal? (top-interp '(local in 7) 1000) "7")

;; A binding's right-hand side uses the outer environment, not a sibling binding.
(check-equal? (top-interp '(local [x = 10] in
                             (local [x = 2] [y = x] in (+ x y))) 1000) "12")
(check-equal? (top-interp '(substring "abcdef" 1 4) 1000) "\"bcd\"")
(check-equal? (top-interp '(substring "hello" 0 5) 1000) "\"hello\"")
(check-equal? (top-interp '(strlen "abc") 1000) "3")
(check-equal? (top-interp '(strlen "") 1000) "0")
(check-equal? (top-interp '(equal? "abc" "abc") 1000) "true")
(check-equal? (top-interp '(equal? (% x -> x) (% x -> x)) 1000) "false")
(check-exn #rx"DRMG" (lambda () (top-interp '(if 0 1 2) 1000)))
(check-exn #rx"DRMG" (lambda () (top-interp '(if "hello" 1 2) 1000)))
(check-exn #rx"DRMG" (lambda () (top-interp '(+ 1 "x") 1000)))
(check-exn #rx"user-error" (lambda () (top-interp '(error "stop") 1000)))
(check-exn #rx"user-error.*\"hello\""
           (lambda () (top-interp '(error "hello") 1000)))
(check-exn #rx"DRMG.*unbound" (lambda () (top-interp 'x 1000)))
(check-equal? (top-interp '+ 1000) "#<primop>")
(check-equal? (top-interp '(% x -> x) 1000) "#<procedure>")
(check-equal? (top-interp '(% -> 5) 1000) "#<procedure>")

;; Tests that the refactored primitive dispatch keeps arity and type checks.
(check-equal? (top-interp '(- 8 3) 1000) "5")
(check-equal? (top-interp '(/ 8 4) 1000) "2")
(check-equal? (top-interp '(<= 8 3) 1000) "false")
(check-equal? (top-interp '(equal? true false) 1000) "false")
(check-equal? (top-interp '(equal? true true) 1000) "true")
(check-equal? (top-interp '(equal? + +) 1000) "false")
(check-equal? (top-interp '(equal? 1 "1") 1000) "false")
(check-equal? (top-interp '(equal? 1 1.0) 1000) "true")
(check-equal? (top-interp '(substring "abc" 3 3) 1000) "\"\"")
(check-equal? (top-interp '(equal? 3 3) 1000) "true")
(check-equal? (top-interp '(equal? 3 4) 1000) "false")
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(+ 1) 1000)))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(strlen "a" "b") 1000)))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(substring "abc" 1) 1000)))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(equal? 1) 1000)))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(error) 1000)))
(check-exn #rx"DRMG.*string" (lambda () (top-interp '(strlen 3) 1000)))
(check-exn #rx"DRMG.*string" (lambda () (top-interp '(substring 5 0 1) 1000)))
(check-exn #rx"DRMG.*indices" (lambda () (top-interp '(substring "abc" 2 1) 1000)))
(check-exn #rx"DRMG.*indices" (lambda () (top-interp '(substring "abc" 0 4) 1000)))
(check-exn #rx"DRMG.*indices" (lambda () (top-interp '(substring "abc" -1 1) 1000)))
(check-exn #rx"DRMG.*indices" (lambda () (top-interp '(substring "abc" 1/2 1) 1000)))
(check-exn #rx"DRMG.*zero" (lambda () (top-interp '(/ 1 0) 1000)))

;; Tests closure capture, primitive shadowing, and eager argument evaluation.
(check-equal?
 (top-interp '(local [x = 10] in
                (local [f = (% y -> (+ x y))] in
                  (local [x = 100] in (f 2)))) 1000)
 "12")
(check-equal? (top-interp '((% + -> (+ 7 2)) -) 1000) "5")
(check-equal? (top-interp '((% -> 9)) 1000) "9")
(check-equal? (top-interp '(if true 10 (/ 1 0)) 1000) "10")
(check-equal? (top-interp '(if false (/ 1 0) 20) 1000) "20")
(check-equal? (top-interp '(((% x -> (% y -> (+ x y))) 10) 5) 1000) "15")
(check-equal? (top-interp
               '(local [x = 10] in
                  (local [f = (% y -> (+ x y))] in
                    (local [x = 100] in
                      (f 5)))) 1000)
              "15")
(check-equal? (top-interp
               '(local [x = 10] in
                  (local [f = (% y -> (+ x y))] in
                    (local [x = 100] in
                      (f x)))) 1000) "110")
(check-equal? (top-interp
               '(local [operation = +] in
                  (operation 10 20)) 1000)
              "30")
(check-equal? (top-interp
               '(local [+ = *] in
                  (+ 3 4)) 1000)
              "12")
(check-equal? (top-interp
               '(local [op = +] in
                  (local [+ = *] in
                    (op 3 4))) 1000)
              "7")
(check-equal? (top-interp
               '((% f -> (f 3))
                 (% x -> (+ x 1))) 1000)
              "4")
(check-equal? (top-interp
               '(local [true = false] in
                  (if true 1 2)) 1000)
              "2")
(check-equal? (top-interp
               '(local [f = (% x -> x)] in
                  (equal? f f)) 1000)
              "false")
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '((% x -> x) 1 2) 1000)))
(check-exn #rx"DRMG.*zero" (lambda () (top-interp '((% x -> 7) (/ 1 0)) 1000)))
(check-exn #rx"DRMG.*zero" (lambda () (top-interp '((% x y -> x) 10 (/ 1 0)) 1000)))
(check-exn #rx"DRMG" (lambda () (top-interp '((% f -> (f 3)) 10) 1000)))
(check-exn #rx"DRMG.*non-function" (lambda () (top-interp '(3 4) 1000)))
(check-exn #rx"DRMG.*unbound"
           (lambda ()
             (top-interp
              '(local [x = 3] [y = x] in y) 1000)))
(check-exn #rx"DRMG.*unknown primitive"
           (lambda ()
             (apply-prim 'unknown '() (NumC 0) (make-initial-store 20))))

;; Tests initial store sizing and the next-free-location pointer.
(check-equal? (vector-length (make-initial-store 20)) 20)
(check-equal? (vector-ref (make-initial-store 20) 0) 16)
(check-equal? (vector-ref (make-initial-store 20) 1) (BoolV #t))
(check-equal? (vector-ref (make-initial-store 20) 2) (BoolV #f))
(check-equal? (vector-ref (make-initial-store 20) 3) (PrimV '+))
(check-exn #rx"DRMG" (lambda () (make-initial-store 0)))
(check-exn #rx"DRMG.*out of memory" (lambda () (make-initial-store 15)))
(check-equal? (top-interp '(+ 1 2) 32) "3")

;; Tests allocation and memory exhaustion.
(define test-sto : Store (make-initial-store 20))
(check-equal? (allocate test-sto 2) 16)
(check-equal? (vector-ref test-sto 0) 18)
(check-equal? (allocate test-sto 2) 18)
(check-equal? (vector-ref test-sto 0) 20)
(check-exn #rx"DRMG.*out of memory"
           (lambda () (allocate test-sto 1)))

;; Tests make-array construction and initialization.
(define array-sto : Store (make-initial-store 20))
(check-equal?
 (apply-prim 'make-array (list (NumV 3) (NumV 7))
             (NumC 0) array-sto)
 (ArrayV 16 3))
(check-equal? (vector-ref array-sto 0) 19)
(check-equal? (vector-ref array-sto 16) (NumV 7))
(check-equal? (vector-ref array-sto 17) (NumV 7))
(check-equal? (vector-ref array-sto 18) (NumV 7))
(check-equal? (serialize (ArrayV 16 3)) "#<array>")
(check-equal? (top-interp '(make-array 3 0) 30) "#<array>")

;; Tests array construction, indexing, and mixed element types.
(check-equal? (top-interp '(array 1 2 3) 30) "#<array>")
(check-equal? (top-interp '(aref (array 10 20 30) 1) 30) "20")
(check-equal? (top-interp '(aref (make-array 3 7) 2) 30) "7")
(check-equal? (top-interp '(aref (array 1 true "hello") 1) 30) "true")
(check-equal? (top-interp '(aref (array 1 true "hello") 2) 30) "\"hello\"")

;; Tests mutation, null, and array identity equality.
(check-equal? (serialize (NullV)) "null")
(check-equal? (top-interp '(aset! (array 1 2) 0 9) 30) "null")
(check-equal?
 (top-interp
  '(local [a = (array 1 2)] in
     (local [unused = (aset! a 0 9)] in
       (aref a 0))) 30)
 "9")
(check-equal?
 (top-interp
  '(equal? (aset! (array 1) 0 2)
           (aset! (array 3) 0 4)) 30)
 "true")
(check-equal?
 (top-interp
  '(local [a = (make-array 2 0)] in
     (equal? a a)) 30)
 "true")
(check-equal?
 (top-interp '(equal? (make-array 2 0) (make-array 2 0)) 30)
 "false")
(check-equal? (top-interp '(equal? (aset! (array 1) 0 2) 2) 30) "false")

;; Tests observable left-to-right evaluation with mutation.
(check-equal?
 (top-interp
  '(local [a = (array 0)] in
     (aref (array (aset! a 0 1)
                  (aset! a 0 2)
                  (aref a 0)) 2)) 40)
 "2")

;; Tests invalid array sizes, indices, types, arities, and memory exhaustion.
(check-exn #rx"DRMG" (lambda () (top-interp '(make-array 0 5) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(make-array -1 5) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(make-array 1.5 5) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(make-array true 0) 30)))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(make-array 3) 30)))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(make-array 3 0 1) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(array) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(aref (array 1 2) 2) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(aref (array 1 2) -1) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(aref (array 1 2) 1/2) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(aref 5 0) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(aset! (array 1 2) 2 9) 30)))
(check-exn #rx"DRMG" (lambda () (top-interp '(aset! (array 1 2) -1 9) 30)))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(aref (array 1)) 30)))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(aset! (array 1) 0) 30)))
(check-exn #rx"DRMG.*out of memory"
           (lambda () (top-interp '(make-array 6 0) 20)))
(check-exn #rx"DRMG.*out of memory"
           (lambda () (top-interp '(array 1 2 3 4 5) 20)))


;; Tests additional array primitive type errors.
(check-exn #rx"DRMG.*positive integer size"
           (lambda () (top-interp '(make-array "three" 0) 30)))
(check-exn #rx"DRMG.*positive integer size"
           (lambda () (top-interp '(make-array 2.0 0) 30)))
(check-exn #rx"DRMG.*aref requires"
           (lambda () (top-interp '(aref true 0) 30)))
(check-exn #rx"DRMG.*aref requires"
           (lambda () (top-interp '(aref (array 1 2) "1") 30)))
(check-exn #rx"DRMG.*aset! requires"
           (lambda () (top-interp '(aset! false 0 5) 30)))
(check-exn #rx"DRMG.*aset! requires"
           (lambda () (top-interp '(aset! (array 1 2) true 5) 30)))

;; Tests array boundaries and allocation.
(check-equal? (top-interp '(aref (array 99) 0) 17) "99")
(check-equal? (top-interp '(aref (array 10 20) 0) 30) "10")
(check-equal? (top-interp '(aref (array 10 20) 1) 30) "20")
(check-exn #rx"DRMG.*out of memory"
           (lambda () (top-interp '(array 1 2) 17)))

;; Tests nested arrays.
(check-equal?
 (top-interp
  '(aref (aref (array (array 1 2) (array 3 4)) 1) 0)
  30)
 "3")

;; Tests that two bindings can reference the same array.
(check-equal?
 (top-interp
  '(local [a = (array 5 6)] in
     (local [b = a] in
       (local [unused = (aset! b 1 17)] in
         (aref a 1))))
  30)
 "17")

;; Tests extending an empty environment and allocating new locations.
(define extra-env-sto : Store (make-initial-store 25))
(check-equal? (extend-env '() '() '() extra-env-sto) '())
(check-equal? (vector-ref extra-env-sto 0) 16)

;; Tests that new bindings shadow existing bindings.
(check-equal?
 (extend-env '(x) (list (NumV 9))
             (list (Binding 'x 3)) extra-env-sto)
 (list (Binding 'x 16) (Binding 'x 3)))

;; Tests that environment extension writes values into the store.
(check-equal? (vector-ref extra-env-sto 16) (NumV 9))
(check-equal? (vector-ref extra-env-sto 0) 17)

;; Tests that existing store values are preserved.
(check-equal? (vector-ref extra-env-sto 3) (PrimV '+))

;; Tests natural-index using the approved integer? and exact? checks.
(check-equal? (natural-index 0) 0)
(check-equal? (natural-index 4) 4)
(check-equal? (natural-index -1) #f)
(check-equal? (natural-index 1/2) #f)
(check-equal? (natural-index 2.0) #f)

;; Tests reading ordinary values without casting store cells.
(check-equal? (read-store (make-initial-store 20) 1) (BoolV #t))
(check-exn #rx"DRMG.*allocation pointer"
           (lambda () (read-store (make-initial-store 20) 0)))
(check-equal? (expect-num (NumV 3) '+ (NumC 3)) 3)
(check-exn #rx"DRMG.*number"
           (lambda () (expect-num (StrV "bad") '+ (NumC 3))))

;; Tests quoted string serialization, including escapes.
(check-equal? (quote-string-rest "" 0) "\"")
(check-equal? (serialize (StrV "")) "\"\"")
(check-equal? (serialize (StrV "a\"b")) "\"a\\\"b\"")
(check-equal? (serialize (StrV "a\\b")) "\"a\\\\b\"")
(check-equal? (serialize (StrV "a\nb\t")) "\"a\\nb\\t\"")
(check-equal? (serialize (NumV 1/2)) "1/2")

;; Tests parsing assignment and a single recursive binding.
(check-equal? (parse '(x := 9)) (SetC 'x (NumC 9)))
(check-equal? (parse '(rocal [f = (% n -> n)] in (f 4)))
              (RecC 'f (LamC '(n) (IdC 'n))
                    (AppC (IdC 'f) (list (NumC 4)))))
(check-equal? (check-invalid-symbols '(rocal)) #t)
(check-exn #rx"DRMG" (lambda () (parse '(if := 3))))
(check-exn #rx"DRMG" (lambda () (parse '(3 := 4))))
(check-exn #rx"DRMG" (lambda () (parse '(x :=))))
(check-exn #rx"DRMG" (lambda () (parse '(x := 1 2))))
(check-exn #rx"DRMG" (lambda () (parse '(rocal in 3))))
(check-exn #rx"DRMG" (lambda () (parse '(rocal [if = 1] in 3))))
(check-exn #rx"DRMG" (lambda () (parse '(rocal [f 1] in 3))))
(check-exn #rx"DRMG" (lambda () (parse '(rocal [f = 1] [g = 2] in 3))))
(check-exn #rx"DRMG" (lambda () (parse '(% rocal -> 1))))

;; Tests mutation results, existing bindings, and lexical scope.
(check-equal? (top-interp '(local [x = 1] in (x := 9)) 40) "null")
(check-equal?
 (top-interp '(local [x = 1] in
                (local [unused = (x := 9)] in x)) 40)
 "9")
(check-exn #rx"DRMG.*unbound" (lambda () (top-interp '(x := 4) 40)))
(check-equal?
 (top-interp '(local [x = 1] in
                (local [get = (% -> x)] in
                  (local [unused = (x := 9)] in (get)))) 50)
 "9")
(check-equal?
 (top-interp '(local [x = 1] in
                (local [f = (% x -> (x := 9))] in
                  (local [unused = (f x)] in x))) 50)
 "1")
(check-equal?
 (top-interp '(local [x = 1] in
                (local [unused = (local [x = 2] in (x := 9))] in x)) 50)
 "1")
(check-equal?
 (top-interp '(local [x = 1] in (equal? (x := 2) (x := 3))) 40)
 "true")

;; Tests recursive closure creation and calling the resulting function.
(check-equal?
 (top-interp '(rocal [fact = (% n ->
                                (if (<= n 1) 1 (* n (fact (- n 1)))))]
                     in (fact 5)) 100)
 "120")
(check-equal?
 (top-interp '(rocal [fact = (% n ->
                                (if (<= n 1) 1 (* n (fact (- n 1)))))]
                     in (fact 0)) 40)
 "1")
(check-equal?
 (top-interp '(local [f = 99] in
                (rocal [f = (% n -> (if (<= n 0) 0 (+ 1 (f (- n 1)))))]
                       in (f 3))) 100)
 "3")
(check-equal?
 (top-interp '((rocal [f = (% n ->
                              (if (<= n 0) 0 (+ 1 (f (- n 1)))))]
                      in f) 4) 100)
 "4")
(check-exn #rx"DRMG.*out of memory"
           (lambda () (top-interp '(rocal [f = (% -> 1)] in f) 16)))

;; Tests function-position and argument evaluation from left to right.
(check-equal?
 (top-interp '(local [x = 0] in
                ((% a b -> x) (x := 1) (x := 2))) 50)
 "2")
(check-equal?
 (top-interp '(local [x = 0] in
                (local [f = (% a -> x)] in
                  ((local [unused = (x := 1)] in f)
                   (x := 2)))) 50)
 "2")
(check-equal?
 (top-interp '(local [x = 0] in
                (local [a = (x := 7)] [b = x] in b)) 50)
 "7")
(check-equal?
 (top-interp '(local [x = 0] in
                (local [unused = (if true (x := 1) (x := 2))] in x)) 50)
 "1")
(check-equal?
 (top-interp '(local [x = 0] in
                (local [unused = (x := (local [u = (x := 2)] in (+ x 3)))]
                  in x)) 50)
 "5")

;; Tests the required while expression with an initially false guard.
(check-equal?
 (top-interp
  (list 'local (list 'while '= while) 'in
        '(local [x = 0] in
           (local [unused = (while (% -> false) (% -> (x := 99)))] in x)))
  100)
 "0")

;; Tests repeated guard/body calls and termination.
(check-equal?
 (top-interp
  (list 'local (list 'while '= while) 'in
        '(local [x = 0] in
           (local [unused = (while (% -> (<= x 3))
                                   (% -> (x := (+ x 1))))] in x)))
  100)
 "4")

;; Tests the required in-order expression using the DRMG6 while function.
(check-equal?
 (top-interp (list 'local (list 'while '= while) 'in
                   (list in-order '(array 1 2 3 4) 4)) 200)
 "true")
(check-equal?
 (top-interp (list 'local (list 'while '= while) 'in
                   (list in-order '(array 1 2 2 4) 4)) 200)
 "false")
(check-equal?
 (top-interp (list 'local (list 'while '= while) 'in
                   (list in-order '(array 4 3 2 1) 4)) 200)
 "false")
(check-equal?
 (top-interp (list 'local (list 'while '= while) 'in
                   (list in-order '(array 1 3 2) 3)) 200)
 "false")
(check-equal?
 (top-interp (list 'local (list 'while '= while) 'in
                   (list in-order '(array 7) 1)) 100)
 "true")
(check-equal?
 (top-interp (list 'local (list 'while '= while) 'in
                   (list in-order '(array -3 -1 1/2 2.5) 4)) 200)
 "true")
(check-equal?
 (top-interp
  '(local [unused = (true := false)] in
     (if true 1 2)) 40)
 "2")
(check-equal?
 (top-interp
  '(local [a = (array 1)] [b = (array 1)] in
     (equal? a b)) 40)
 "false")
(check-equal?
 (top-interp
  '(local [a = (array 1)] in
     (local [b = a] in
       (local [unused = (aset! b 0 8)] in
         (aref a 0)))) 40)
 "8")
(check-equal?
 (top-interp
  '((rocal [f = (% n ->
                   (if (<= n 0) 0 (+ 1 (f (- n 1)))))]
           in f) 5) 100)
 "5")
(check-equal?
 (top-interp '(aref (make-array 1 42) 0) 17)
 "42")
(define invalid-pointer-sto : Store (make-initial-store 20))
(vector-set! invalid-pointer-sto 0 (NumV 5))
(check-exn #rx"DRMG.*invalid store allocation pointer"
           (lambda ()
             (allocate invalid-pointer-sto 1)))
(check-equal? (serialize (StrV "a\rb")) "\"a\\rb\"")
(check-equal? (serialize (StrV "a\ab")) "\"a\\ab\"")
(check-equal? (serialize (StrV "a\bb")) "\"a\\bb\"")
(check-equal? (serialize (StrV "a\vb")) "\"a\\vb\"")
(check-equal? (serialize (StrV "a\fb")) "\"a\\fb\"")
(check-exn #rx"DRMG.*unbound"
           (lambda () (top-interp 'missing 30)))
(check-exn #rx"DRMG.*out of memory"
           (lambda () (top-interp '(make-array 6 0) 20)))
(check-exn #rx"DRMG.*out of memory"
           (lambda () (top-interp '(make-array 1 0) 15)))
(check-exn #rx"DRMG.*allocation pointer"
           (lambda ()
             (read-store (make-initial-store 20) 0)))
