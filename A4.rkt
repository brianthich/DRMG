#lang typed/racket

(require typed/rackunit)

;; Progress: Implements DRMG4 parsing, environments, closures, primitives,
;; booleans, strings, conditionals, local desugaring, serialization, and tests.

(define-type ExprC (U NumC BoolC StrC IdC IfC LamC AppC))
(struct NumC ([n : Real]) #:transparent)
(struct BoolC ([b : Boolean]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct IdC ([name : Symbol]) #:transparent)
(struct IfC ([test : ExprC] [yes : ExprC] [no : ExprC]) #:transparent)
(struct LamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)

(define-type Value (U NumV BoolV StrV ClosureV PrimV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct ClosureV ([params : (Listof Symbol)] [body : ExprC] [env : Environment]) #:transparent)
(struct PrimV ([name : Symbol]) #:transparent)
(struct Binding ([name : Symbol] [value : Value]) #:transparent)
(define-type Environment (Listof Binding))

;; Reserved syntax words cannot be used as identifiers; primitive names can.
(define reserved (set 'if '= 'local '% '-> 'in))

;; Returns true if the supplied list contains a reserved syntax word.
(define (check-invalid-symbols [lst : (Listof Any)]) : Boolean
  (match lst
    [(cons f r)
     (if (set-member? reserved f) #t (check-invalid-symbols r))]
    ['() #f]))

;; Looks up a name in an environment and reports an error when absent.
(: lookup (-> Symbol Environment Value))
(define (lookup name env)
  (match env
    ['() (error 'DRMG "unbound identifier: ~e" name)]
    [(cons (Binding n v) rest) (if (equal? n name) v (lookup name rest))]))

;; Adds parameter/value bindings before a saved environment, preserving shadowing.
(define (extend-env [params : (Listof Symbol)]
                    [values : (Listof Value)]
                    [env : Environment]) : Environment
  (match* (params values)
    [('() '()) env]
    [((cons p ps) (cons v vs))
     (cons (Binding p v) (extend-env ps vs env))]
    [(_ _) (error 'DRMG "wrong arity: parameters ~e, values ~e" params values)]))

;; Parses DRMG4 syntax into its expression representation.
(: parse (-> Sexp ExprC))
(define (parse s)
  (match s
    [(? real? n) (NumC n)]
    [(? string? str) (StrC str)]
    [(? symbol? id)
     (if (check-invalid-symbols (list id))
         (error 'DRMG "reserved word used as identifier in ~e" s)
         (IdC id))]
    [(list 'if tst yes no) (IfC (parse tst) (parse yes) (parse no))]
    [(list '% (? symbol? params) ... '-> body)
     (define ps (cast params (Listof Symbol)))
     (if (check-duplicates ps)
         (error 'DRMG "duplicate function parameter in ~e" s)
         (if (check-invalid-symbols ps)
             (error 'DRMG "reserved function parameter in ~e" s)
             (LamC ps (parse body))))]
    [(list 'local bindings ... 'in body)
     (define pairs : (Listof (Pairof Symbol ExprC))
       (for/list : (Listof (Pairof Symbol ExprC)) ([b bindings])
         (match b
           [(list (? symbol? name) '= rhs)
            (if (check-invalid-symbols (list name))
                (error 'DRMG "reserved local name in ~e" s)
                (cons name (parse (cast rhs Sexp))))]
           [_ (error 'DRMG "malformed local binding in ~e" b)])))
     (define names
       (for/list : (Listof Symbol) ([pair pairs])
         (match pair [(cons name rhs) name])))
     ;; The binding values are already parsed; desugar directly into the AST.
     (if (check-duplicates names)
         (error 'DRMG "duplicate local name in ~e" s)
         (AppC (LamC names (parse body))
               (for/list : (Listof ExprC) ([pair pairs])
                 (match pair [(cons name rhs) rhs]))))]
    [(list f args ...)
     (AppC (parse f)
           (for/list : (Listof ExprC) ([arg args])
             (parse arg)))]
    [_ (error 'DRMG "invalid syntax in ~e" s)]))

;; Serializes a value using the required DRMG4 representation.
(: serialize (-> Value String))
(define (serialize v)
  (match v
    [(NumV n) (~v n)]
    [(BoolV #t) "true"]
    [(BoolV #f) "false"]
    [(StrV s) (~v s)]
    [(ClosureV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]))

;; Retrieves a number from a value or raises a helpful DRMG error.
(: expect-num (-> Value Symbol ExprC Real))
(define (expect-num v op whole)
  (match v [(NumV n) n] [_ (error 'DRMG "~a expected a number; received ~a in ~e" op (serialize v) whole)]))

;; Applies a primitive operator to already evaluated arguments.
(: apply-prim (-> Symbol (Listof Value) ExprC Value))
(define (apply-prim op vs whole)
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
    [('strlen (list _)) (error 'DRMG "strlen expected a string in ~e" whole)]
    [('substring (list (StrV s) (NumV start) (NumV stop)))
     (if (and (exact-nonnegative-integer? start)
              (exact-nonnegative-integer? stop)
              (<= start stop)
              (<= stop (string-length s)))
         (StrV (substring s start stop))
         (error 'DRMG "substring indices must be natural, in range, and ordered in ~e" whole))]
    [('substring (list _ _ _))
     (error 'DRMG "substring expected a string and two natural indices in ~e" whole)]
    [('equal? (list a b))
     (BoolV (match* (a b)
       [((NumV x) (NumV y)) (= x y)]
       [((BoolV x) (BoolV y)) (equal? x y)]
       [((StrV x) (StrV y)) (equal? x y)]
       [(_ _) #f]))]
    [('error (list v))
     (error 'DRMG "user-error ~a in ~e" (serialize v) whole)]
    [((or '+ '- '* '/ '<= 'strlen 'substring 'equal? 'error) _)
     (error 'DRMG "wrong arity for ~a: received ~a arguments in ~e" op (length vs) whole)]
    [(_ _) (error 'DRMG "unknown primitive ~e in ~e" op whole)]))

;; Evaluates an expression in an environment using eager application.
(: interp (-> ExprC Environment Value))
(define (interp e env)
  (match e
    [(NumC n) (NumV n)]
    [(BoolC b) (BoolV b)]
    [(StrC s) (StrV s)]
    [(IdC name) (lookup name env)]
    [(IfC tst yes no)
     (match (interp tst env)
       [(BoolV #t) (interp yes env)]
       [(BoolV #f) (interp no env)]
       [v (error 'DRMG "if test must be boolean; received ~a in ~e" (serialize v) e)])]
    [(LamC ps body) (ClosureV ps body env)]
    [(AppC f args)
     (define fv (interp f env))
     (define av
       (for/list : (Listof Value) ([arg args])
         (interp arg env)))
     (match fv
       [(ClosureV ps body saved)
        (if (= (length ps) (length av))
            (interp body (extend-env ps av saved))
            (error 'DRMG "wrong arity: function expected ~a arguments, received ~a in ~e"
                   (length ps) (length av) e))]
       [(PrimV op) (apply-prim op av e)]
       [_ (error 'DRMG "attempted to call a non-function value in ~e" e)])]))

;; Provides primitive and boolean bindings for a top-level DRMG4 program.
(: top-env Environment)
(define top-env
  (cons (Binding 'true (BoolV #t))
        (cons (Binding 'false (BoolV #f))
              (for/list : Environment ([n '(+ - * / <= substring strlen equal? error)])
                (Binding n (PrimV n))))))

;; Parses, evaluates, and serializes one DRMG4 program expression.
(: top-interp (-> Sexp String))
(define (top-interp s) (serialize (interp (parse s) top-env)))


;; Tests for identifier validation and environment extension.
(check-equal? (check-invalid-symbols '()) #f)
(check-equal? (check-invalid-symbols '(+ true value)) #f)
(check-equal? (check-invalid-symbols '(x if y)) #t)
(check-equal? (lookup 'x (list (Binding 'x (NumV 4)))) (NumV 4))
(check-exn #rx"DRMG.*unbound" (lambda () (lookup 'x '())))
(check-equal? (extend-env '(x) (list (NumV 2)) (list (Binding 'x (NumV 10))))
              (list (Binding 'x (NumV 2)) (Binding 'x (NumV 10))))
(check-exn #rx"DRMG.*arity" (lambda () (extend-env '(x) '() '())))
(check-exn #rx"DRMG.*arity" (lambda () (extend-env '() (list (NumV 2)) '())))

;; Tests parser support for literals, application, functions, and local desugaring.
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
(check-equal? (interp (BoolC #t) top-env) (BoolV #t))
(check-equal? (interp (BoolC #f) top-env) (BoolV #f))
(check-equal? (top-interp '(+ 1 2)) "3")
(check-equal? (top-interp '(if (<= 2 3) "yes" "no")) "\"yes\"")
(check-equal? (top-interp '((% x -> (* x x)) 5)) "25")
(check-equal? (top-interp '(local [x = 4] [y = 6] in (+ x y))) "10")
(check-equal? (top-interp '(local in 7)) "7")

;; A binding's right-hand side uses the outer environment, not a sibling binding.
(check-equal? (top-interp '(local [x = 10] in
                           (local [x = 2] [y = x] in (+ x y)))) "12")
(check-equal? (top-interp '(substring "abcdef" 1 4)) "\"bcd\"")
(check-equal? (top-interp '(substring "hello" 0 5)) "\"hello\"")
(check-equal? (top-interp '(strlen "abc")) "3")
(check-equal? (top-interp '(strlen "")) "0")
(check-equal? (top-interp '(equal? "abc" "abc")) "true")
(check-equal? (top-interp '(equal? (% x -> x) (% x -> x))) "false")
(check-exn #rx"DRMG" (lambda () (top-interp '(if 0 1 2))))
(check-exn #rx"DRMG" (lambda () (top-interp '(if "hello" 1 2))))
(check-exn #rx"DRMG" (lambda () (top-interp '(+ 1 "x"))))
(check-exn #rx"user-error" (lambda () (top-interp '(error "stop"))))
(check-exn #rx"user-error.*\"hello\""
           (lambda () (top-interp '(error "hello"))))
(check-exn #rx"DRMG.*unbound" (lambda () (top-interp 'x)))
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '(% x -> x)) "#<procedure>")
(check-equal? (top-interp '(% -> 5)) "#<procedure>")

;; Tests that the refactored primitive dispatch keeps arity and type checks.
(check-equal? (top-interp '(- 8 3)) "5")
(check-equal? (top-interp '(/ 8 4)) "2")
(check-equal? (top-interp '(<= 8 3)) "false")
(check-equal? (top-interp '(equal? true false)) "false")
(check-equal? (top-interp '(equal? true true)) "true")
(check-equal? (top-interp '(equal? + +)) "false")
(check-equal? (top-interp '(equal? 1 "1")) "false")
(check-equal? (top-interp '(equal? 1 1.0)) "true")
(check-equal? (top-interp '(substring "abc" 3 3)) "\"\"")
(check-equal? (top-interp '(equal? 3 3)) "true")
(check-equal? (top-interp '(equal? 3 4)) "false")
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(+ 1))))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(strlen "a" "b"))))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(substring "abc" 1))))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(equal? 1))))
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '(error))))
(check-exn #rx"DRMG.*string" (lambda () (top-interp '(strlen 3))))
(check-exn #rx"DRMG.*string" (lambda () (top-interp '(substring 5 0 1))))
(check-exn #rx"DRMG.*indices" (lambda () (top-interp '(substring "abc" 2 1))))
(check-exn #rx"DRMG.*indices" (lambda () (top-interp '(substring "abc" 0 4))))
(check-exn #rx"DRMG.*indices" (lambda () (top-interp '(substring "abc" -1 1))))
(check-exn #rx"DRMG.*indices" (lambda () (top-interp '(substring "abc" 1/2 1))))
(check-exn #rx"DRMG.*zero" (lambda () (top-interp '(/ 1 0))))

;; Tests closure capture, primitive shadowing, and eager argument evaluation.
(check-equal?
 (top-interp '(local [x = 10] in
                (local [f = (% y -> (+ x y))] in
                  (local [x = 100] in (f 2)))))
 "12")
(check-equal? (top-interp '((% + -> (+ 7 2)) -)) "5")
(check-equal? (top-interp '((% -> 9))) "9")
(check-equal? (top-interp '(if true 10 (/ 1 0))) "10")
(check-equal? (top-interp '(if false (/ 1 0) 20)) "20")
(check-equal? (top-interp '(((% x -> (% y -> (+ x y))) 10) 5)) "15")
(check-equal? (top-interp
               '(local [x = 10] in
                  (local [f = (% y -> (+ x y))] in
                    (local [x = 100] in
                      (f 5)))))
              "15")
(check-equal? (top-interp
               '(local [x = 10] in
                  (local [f = (% y -> (+ x y))] in
                    (local [x = 100] in
                      (f x))))) "110")
(check-equal? (top-interp
               '(local [operation = +] in
                  (operation 10 20)))
              "30")
(check-equal? (top-interp
               '(local [+ = *] in
                  (+ 3 4)))
              "12")
(check-equal? (top-interp
               '(local [op = +] in
                  (local [+ = *] in
                    (op 3 4))))
              "7")
(check-equal? (top-interp
               '((% f -> (f 3))
                 (% x -> (+ x 1))))
              "4")
(check-equal? (top-interp
               '(local [true = false] in
                  (if true 1 2)))
              "2")
(check-equal? (top-interp
               '(local [f = (% x -> x)] in
                  (equal? f f)))
              "false")
(check-exn #rx"DRMG.*arity" (lambda () (top-interp '((% x -> x) 1 2))))
(check-exn #rx"DRMG.*zero" (lambda () (top-interp '((% x -> 7) (/ 1 0)))))
(check-exn #rx"DRMG.*zero" (lambda () (top-interp '((% x y -> x) 10 (/ 1 0)))))
(check-exn #rx"DRMG" (lambda () (top-interp '((% f -> (f 3)) 10))))
(check-exn #rx"DRMG.*non-function" (lambda () (top-interp '(3 4))))
(check-exn #rx"DRMG.*unbound"
           (lambda ()
             (top-interp
              '(local [x = 3] [y = x] in y))))
(check-exn #rx"DRMG.*unknown primitive"
           (lambda ()
             (apply-prim 'unknown '() (NumC 0))))

