#lang typed/racket

(require typed/rackunit)

;; Arith data definitions
(define-type ExprC (U numC binopC ifleq0? idC appC))
(struct numC ([n : Real]) #:transparent)
(struct binopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct fundefC ([name : Symbol] [params : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct ifleq0? ([n : ExprC] [t : ExprC] [f : ExprC]) #:transparent)
(struct idC ([name : Symbol]) #:transparent)
(struct appC ([name : Symbol] [params : (Listof ExprC)]) #:transparent)
(define-type Environment (Listof Binding))
(struct Binding ([name : Symbol] [value : Real]) #:transparent)

;; Takes two real numbers and returns the quotient if valid, or reports division by zero
(define (sf [l : Real] [r : Real]): Real
  (if (zero? r)
      (error 'DRMG "division by zero: ~e" (list '/ l r))
      (/ l r)))

;; Hash table for operator symbols
(define ops
        (hash '+ +
              '- -
              '* *
              '/ sf))

;; Hash table for reserved symbols
(define reserved (set
             '=
             'ifleq0?))

;; Takes a name and an env and sees if the name is in the env, if so returns its value
(define (lookup [name : Symbol] [env : Environment]) : Real
  (match env
    [(cons (Binding n v) r) #:when (equal? n name) v]
    [(cons _ r) (lookup name r)]
    ['() (error 'DRMG "Binding ~e not found in environment: ~e" name env)]))

;; Takes an s expression and returns its ArithC form
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (numC n)]
    [(? symbol? s) #:when (not (check-invalid-symbols (list s))) (idC s)]
    [(list (? symbol? op) l r) #:when (hash-has-key? ops op)
                               (binopC op (parse l) (parse r))]
    [(list 'ifleq0? n l r) (ifleq0? (parse n) (parse l) (parse r))]
    [(list (? symbol? s) params ...) #:when (not (check-invalid-symbols (list s)))
                                     (appC s
                                           (for/list : (Listof ExprC) ([param params])
                                             (parse param)))]
    [_ (error 'DRMG "invalid syntax: ~e" s)]))

;; Evaluates an ExprC using the supplied function definitions
(define (interp [a : ExprC] [funs : (Listof fundefC)] [env : Environment]) : Real
  (match a
    [(numC n) n]
    [(binopC op l r)
     ((hash-ref ops op
                (lambda () (error 'DRMG "unknown operator: ~e" op)))
      (interp l funs env) (interp r funs env))]
    [(ifleq0? n t f)
     (if (<= (interp n funs env) 0)
         (interp t funs env)
         (interp f funs env))]
    [(idC n) (lookup n env)]
    [(appC n args)
     (match (get-fundef n funs)
       [(fundefC name params body)
        (if (= (length params) (length args))
            (interp
             body
             funs
             (for/list : Environment ([param params] [arg args])
               (Binding param (interp arg funs env))))
            (error 'DRMG "wrong arity: ~e" a))])]))

;; Parses a statment for bad syntax and returns a fundef if valid
(define (parse-fundef [s : Sexp]) : fundefC
  (match s
    [(list (? symbol? n) (? symbol? l) ... '= e)
     #:when (and
             (not (check-duplicates l))
             (not (check-invalid-symbols (cast l (Listof Symbol))))
             (not (check-invalid-symbols (list n))))
     (fundefC n (cast l (Listof Symbol)) (parse e))]
    [_ (error 'DRMG "bad syntax: ~e" s)]))

;; Checks if list has symbols that are reserved or are operators
(define (check-invalid-symbols [lst : (Listof Any)]) : Boolean
  (match lst
    [(cons f r) #:when (or (set-member? reserved f) (hash-has-key? ops f)) #t]
    [(cons f r) (check-invalid-symbols r)]
    ['() #f]))

;; Parses a whole program and evaluates main
(define (top-interp [s : Sexp]) : Real
  (interp-fns (parse-prog s)))

;; Finds a function definition by name, or reports an undefined function
(define (get-fundef [name : Symbol] [f : (Listof fundefC)]) : fundefC
  (match f
    ['() (error 'DRMG "undefined function: ~e" name)]
    [(cons f r) (if (equal? name (fundefC-name f))
                    f
                    (get-fundef name r))]))

;; Replaces occurrences of a parameter in an expression with a numeric value
(define (subst [body : ExprC] [name : Symbol] [value : Real]) : ExprC
  (match body
    [(numC n) body]
    [(idC n)
     (if (equal? n name)
         (numC value)
         body)]
    [(binopC op l r)
     (binopC op (subst l name value) (subst r name value))]
    [(ifleq0? n t f)
     (ifleq0? (subst n name value)
              (subst t name value)
              (subst f name value))]
    [(appC n params)
     (appC n
           (for/list : (Listof ExprC) ([param params])
             (subst param name value)))]))

;; Replaces each parameter in a body with its corresponding numeric value
(define (subst-many [body : ExprC] [params : (Listof Symbol)] [values : (Listof Real)]) : ExprC
  (match* (params values)
    [('() '()) body]
    [((cons p ps) (cons v vs))(subst-many (subst body p v) ps vs)]
    [(_ _) (error 'DRMG "wrong arity: parameters ~e, values ~e, body ~e" params values body)]))

;; Parses a program and rejects duplicate function names
(define (parse-prog [s : Sexp]) : (Listof fundefC)
  (match s
    [(? list? l) (match (for/list : (Listof fundefC) ([f (cast l (Listof Sexp))])
                          (parse-fundef f))
                   [funs
                    (if (check-duplicates (for/list : (Listof Symbol) ([f funs]) (fundefC-name f)))
                        (error 'DRMG "bad syntax: duplicate function names in ~e" s)
                        funs)])]
    [_ (error 'DRMG "bad syntax: expected a list of function definitions: ~e" s)]))

;; Evaluates a program by calling main with no arguments
(define (interp-fns [funs : (Listof fundefC)]) : Real
  (interp (appC 'main '()) funs '()))

;; Tests for sf
(check-equal? (sf 8 4) 2)
(check-equal? (sf 5 2) 5/2)
(check-equal? (sf -8 4) -2)
(check-exn #rx"division by zero" (lambda () (sf 1 0)))
(check-exn #rx"division by zero" (lambda () (sf 1 0.0)))

;; Tests for parse
(check-equal? (parse '1) (numC 1))
(check-equal? (parse '(+ 1 2)) (binopC '+ (numC 1) (numC 2)))
(check-equal? (parse '(* 1 2)) (binopC '* (numC 1) (numC 2)))
(check-equal? (parse '(* (+ 1 2) (* 3 4))) (binopC '* (binopC '+ (numC 1) (numC 2)) (binopC '* (numC 3) (numC 4))))
(check-equal? (parse '(* (* (+ 1 2) (* 3 4)) 5))
              (binopC '*
                      (binopC '* (binopC '+ (numC 1) (numC 2))
                              (binopC '* (numC 3) (numC 4)))
                      (numC 5)))
(check-equal? (parse 'a) (idC 'a))
(check-exn #rx"invalid syntax: #t" (lambda () (parse #t)))
(check-equal? (parse '(a))
              (appC 'a '()))
(check-equal? (parse '(a 1 2))
              (appC 'a (list (numC 1) (numC 2))))
(check-equal? (parse '(a b c))
              (appC 'a (list (idC 'b) (idC 'c))))
(check-equal? (parse '(a (+ 1 2) 3))
              (appC 'a
                    (list (binopC '+ (numC 1) (numC 2))
                          (numC 3))))
(check-exn #rx"invalid syntax" (lambda () (parse '(+ 1))))
(check-exn #rx"invalid syntax" (lambda () (parse '(- 1 2 3))))
(check-exn #rx"invalid syntax" (lambda () (parse '(*))))
(check-exn #rx"invalid syntax" (lambda () (parse '(/ 1))))
(check-exn #rx"invalid syntax" (lambda () (parse '(= 1 2))))
(check-exn #rx"invalid syntax" (lambda () (parse '(ifleq0? 1 2))))
(check-exn #rx"invalid syntax" (lambda () (parse '(ifleq0?))))
(check-equal? (interp (parse '(a 1 2)) (list (parse-fundef '(a b c = (+ b c)))) '())3)
(check-exn #rx"wrong arity" (lambda ()(interp (parse '(a 1)) (list (parse-fundef '(a b c = (+ b c)))) '())))
(check-exn #rx"Binding 'a not found in environment: '()" (lambda () (interp (idC 'a) '() '())))
(check-exn #rx"division by zero" (lambda () (interp (parse '(a (/ 1 0))) (list (parse-fundef '(a b = 2))) '())))

;; Tests for interp
(check-equal? (interp (numC 1) '() '()) 1)
(check-equal? (interp (binopC '+ (numC 1) (numC 2)) '() '()) 3)
(check-equal? (interp (binopC '- (numC 8) (numC 3)) '() '()) 5)
(check-equal? (interp (binopC '* (numC 3) (numC 4)) '() '()) 12)
(check-equal? (interp (binopC '/ (numC 8) (numC 4)) '() '()) 2)
(check-equal? (interp (binopC '/ (numC 1) (numC 2)) '() '()) 1/2)
(check-exn #rx"unknown operator: 'lebron" (lambda () (interp (binopC 'lebron (numC 2) (numC 3)) '() '())))
(check-equal? (interp
               (binopC '*
                       (binopC '+ (numC 1) (numC 2))
                       (binopC '+ (numC 3) (numC 4))) '() '()) 21)
(check-equal? (interp (ifleq0? (numC 1) (numC 1) (numC 2)) '() '()) 2)
(check-equal? (interp (ifleq0?
                       (binopC '+ (numC 1) (numC 2))
                               (numC 1)
                               (numC 2)) '() '()) 2)
(check-equal? (interp (ifleq0?
                       (binopC '+ (numC 1) (numC 2))
                       (numC 1)
                       (binopC '+ (numC 1) (numC 2))) '() '()) 3)
(check-equal? (interp (ifleq0?
                       (binopC '- (numC 1) (numC 2))
                       (binopC '+ (numC 1) (numC 2))
                       (numC 1)) '() '()) 3)

;; Tests for parse-fundef
(check-equal? (parse-fundef '(a = 1))(fundefC 'a '() (numC 1)))
(check-equal? (parse-fundef '(a b = 2)) (fundefC 'a '(b) (numC 2)))
(check-equal? (parse-fundef '(a b c = 3)) (fundefC 'a '(b c) (numC 3)))
(check-equal? (parse-fundef '(a b c = (+ 1 (* 2 3))))
              (fundefC 'a '(b c) (binopC '+ (numC 1) (binopC '* (numC 2) (numC 3)))))
(check-exn #rx"invalid syntax" (lambda () (parse-fundef '(a = (+ 1)))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a b b = 1))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a b c c = 1))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a + = 1))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a b ifleq0? = 1))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(1 = 2))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a 1 = 2))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a (b c) = 1))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a b 1))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a b =))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(a = 1 2))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '())))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(+ = 1))))
(check-exn #rx"bad syntax" (lambda () (parse-fundef '(ifleq0? b = 1))))

;; Tests for check-invalid-symbols
(check-equal? (check-invalid-symbols '()) #f)
(check-equal? (check-invalid-symbols '(lebron)) #f)
(check-equal? (check-invalid-symbols '(a b c)) #f)
(check-equal? (check-invalid-symbols '(a b c +)) #t)
(check-equal? (check-invalid-symbols '(a b ifleq0? c)) #t)
(check-equal? (check-invalid-symbols '(a b = c +)) #t)

;; Tests for top-interp
(check-equal? (top-interp '((main = 1))) 1)
(check-equal? (top-interp '((main = (+ 1 2)))) 3)
(check-equal? (top-interp '((main = (* 1 2)))) 2)
(check-equal? (top-interp '((main = (/ 1 1)))) 1)
(check-equal? (top-interp '((main = (* (+ 1 2) (* 3 4))))) 36)
(check-equal? (top-interp '((main = (/ (* (+ 1 2) (* 3 4)) 2)))) 18)
(check-equal? (top-interp '((main = (ifleq0? 1 2 3)))) 3)
(check-equal? (top-interp '((main = (ifleq0? (+ 1 2) 1 2)))) 2)
(check-equal? (top-interp '((main = (ifleq0? (- 1 2) (+ 1 2) 2)))) 3)
(check-equal? (top-interp '((a b c = (+ b c)) (main = (a 1 2)))) 3)
(check-exn #rx"undefined function" (lambda () (top-interp '((a = 1)))))
(check-exn #rx"wrong arity" (lambda () (top-interp '((main a = a)))))

;; Tests for get-fundef
(check-equal? (get-fundef 'a (list (fundefC 'a '() (numC 1)))) (fundefC 'a '() (numC 1)))
(check-equal? (get-fundef 'b (list (fundefC 'a '() (numC 1)) (fundefC 'b '(c) (idC 'c)))) (fundefC 'b '(c) (idC 'c)))
(check-exn #rx"undefined function" (lambda () (get-fundef 'a '())))
(check-exn #rx"undefined function" (lambda () (get-fundef 'a (list (fundefC 'b '() (numC 2))))))

;; Tests for subst
(check-equal? (subst (numC 1) 'a 2) (numC 1))
(check-equal? (subst (idC 'a) 'a 1) (numC 1))
(check-equal? (subst (idC 'b) 'a 1) (idC 'b))
(check-equal? (subst (binopC '+ (idC 'a) (numC 2)) 'a 1) (binopC '+ (numC 1) (numC 2)))
(check-equal? (subst (ifleq0? (idC 'a) (idC 'a) (numC 2)) 'a 1) (ifleq0? (numC 1) (numC 1) (numC 2)))
(check-equal? (subst (appC 'a (list (idC 'a) (idC 'b))) 'a 1) (appC 'a (list (numC 1) (idC 'b))))

;; Tests for subst-many
(check-equal? (subst-many (numC 1) '() '()) (numC 1))
(check-equal? (subst-many (idC 'a) '(a) '(1)) (numC 1))
(check-equal? (subst-many (binopC '+ (idC 'a) (idC 'b)) '(a b) '(1 2))(binopC '+ (numC 1) (numC 2)))
(check-exn #rx"wrong arity" (lambda ()(subst-many (idC 'a) '(a b) '(1))))
(check-exn #rx"wrong arity" (lambda () (subst-many (idC 'a) '(a) '(1 2))))

;; Tests for parse-prog
(check-equal? (parse-prog '()) '())
(check-equal? (parse-prog '((a = 1))) (list (fundefC 'a '() (numC 1))))
(check-equal? (parse-prog '((a = 1) (b c = c))) (list (fundefC 'a '() (numC 1)) (fundefC 'b '(c) (idC 'c))))
(check-exn #rx"duplicate function names" (lambda () (parse-prog '((a = 1) (a = 2)))))
(check-exn #rx"bad syntax" (lambda () (parse-prog 'a)))
(check-exn #rx"bad syntax" (lambda () (parse-prog '((a b b = 1)))))

;; Tests for interp-fns
(check-equal? (interp-fns (list (fundefC 'main '() (numC 1)))) 1)
(check-exn #rx"undefined function" (lambda () (interp-fns '())))
(check-exn #rx"wrong arity" (lambda () (interp-fns (list (fundefC 'main '(a) (numC 1))))))

;; Tests for lookup
(check-equal? (lookup 'x (list (Binding 'x 10))) 10)
(check-equal? (lookup 'y (list (Binding 'x 10) (Binding 'y 20))) 20)
(check-exn #rx"Binding 'z not found in environment: '()" (lambda () (lookup 'z '())))