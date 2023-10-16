#lang play
(print-only-errors #f)

#|
----- Práctica # -----

Estudiante: Rodrigo Guardia Ramirez

Asignatura: Programación Funcional

|#
#|
<FAE> ::= <num> | <bool>
        | (+ <FAE> <FAE>)
        | (- <FAE> <FAE>)
        | (gt n1 n2)
        | (lt n1 n2)
        | (if-tf <FAE> <FAE> <FAE>)
        | (with id-name named-expr body-expr)
        | <id>
        | (app <id> <FAE>)
        | (fun <id> <FAE>)
|#
; (foo 4)-> {app 'foo      (num 4)}
;                 fun-name arg
(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [add l r]                               ; (+ <FAE> <FAE>)
  [sub l r]                               ; (- <FAE> <FAE>)
  [gt l r]
  [lt l r]
  [if-tf c et ef]                         ; (if-tf <FAE> <FAE> <FAE>)
  ;[with id-name named-expr body-expr]     ; (with <id> <FAE> <FAE>)
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <id> <FAE>)
  [fun arg body]
  [prim name args]
  [string s]
  [concat exprs]
)

(define primitives
  (list (cons '+ +)
        (cons '- -)
        (cons '* *)
        (cons '/ /)
        (cons '< <)
        (cons '> >)
        (cons '== eq?)
        (cons '!= (λ (h t) (not (eq? h t))))
        (cons '<= <=)
        (cons '>= >=)
        (cons 'and  (λ (h t) (and  h t)))
        (cons 'or (λ (h t) (or  h t)))
        (cons 'string string-append)
        )
  )

;(apply (car (assq '+ primitives)) '(1 2 3 4))
  
(deftype Val
  (valV v)
  (closureV arg body env) ;closure = fun + env
  (promiseV expr env cache) ;promise = expr + env
  )

#|
<env> ::= (mtEnv)
          | (aEnv <id> <val> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id val env)
  )

; empty-env -> (mtEnv)
(define empty-env (mtEnv))

; extend-env:: <id> <val> <env> -> <env>
(define extend-env aEnv)

; env-lookup :: <id> <env> -> <val>
; buscar el valor de una variable dentro del ambiente
(define (env-lookup x env)
  (match env
    [(mtEnv) (error "undefined: " x)]
    [(aEnv id val en) (if(eq? x id) val (env-lookup x en))]
    )
  )

;(test (run env-lookup 'y (('x 1 ('y 4 (mtEnv)))) ) 4)
; parse: Src -> Expr
; parsea codigo fuente
(define (parse src)
  (match src
    [(? number?) (num src)]
    [(? boolean?) (bool src)]
    [(? symbol?) (id src)]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (list id-name named-exp) body) (app (fun id-name (parse body)) (parse named-exp))]
    [(list 'fun (list x) body) (fun x (parse body))]
    [(list f arg) (app (parse f) (parse arg))]
    [(list 'string s) (string s)]
    [(list 'concat exprs) (concat (map parse exprs))] 
    [(cons prim-name args)(prim prim-name (map parse args))]
    )
  )

;prim-ops: name args -> val
(define (prim-ops name args)
  (let ([vals (map (λ (x) (valV-v x)) args)])
    (valV (apply (cdr (assq name primitives)) vals ))
    )
  )

; interp :: Expr Env -> val
; interpreta una expresion
(define (interp expr env)
  (match expr
    [(num n) (valV n)]
    [(bool b) (valV b)]
    [(id x) (env-lookup x env)]; busca el valor de x en env
    [(string s) (valV s)]
    [(prim prim-name args)(prim-ops prim-name (map (λ (x) (strict (interp x env))) args))]
    [(if-tf c et ef) (if (strict (interp c env))(strict (interp et env))(strict (interp ef env)))]
    [(fun x body) (closureV x body env)]
    [(app f e)
     (def (closureV arg body fenv) (strict (interp f env)))
     ;(interp body fundefs(extend-env arg (interp e fundefs env) env)); scope dinamico
     (interp body(extend-env arg 
                             (promiseV e env (box #f))
                             fenv)) ;scope statico
     ]
    [(concat exprs) (valV (string-append (map (λ (x) (strict (interp x env))) exprs)))]
))

(define (search-for-ids expr)
  (match expr
    [(cons (id x) tail) #f]
    [(cons head tail) (and #t (search-for-ids tail))]
    ['() #t]
    
    )
  )

;Discutido y apoyado por Chris Rivero:
(define (constant-folding expr)
  (match expr
    [(num n) (num n)]
    [(bool b) (bool b)]
    [(id x) (id x)]
    [(prim prim-name args) (if (search-for-ids args)
                               (parse (valV-v (interp (prim prim-name args) mtEnv)))
                               (prim prim-name (map constant-folding args))
                               )]
    [(if-tf c et ef) (if-tf (constant-folding c)
                         (constant-folding et)
                         (constant-folding ef))]
    [(fun arg body) (fun  arg (constant-folding body))] 
    [(app f e)
     (app (constant-folding f) (constant-folding e))]
    )
  )

;Llegue hasta donde pude
(define (constant-propagation expr)
  (match expr
    [(num n) (num n)]
    [(bool b) (bool b)]
    [(id x) (id x)]
    [(cons h t)  (parse (valV-v (interp h mtEnv)))  (parse (valV-v (interp (car t) mtEnv)))]
    [(fun arg body) (fun  arg (constant-propagation body))] 
    [(app f e)
     (app (constant-propagation f) (constant-propagation e))]
    [(prim prim-name args) (constant-propagation args)]
    )
  )




; valV :valV valV -> vale
(define (valV+ s1 s2)
  (valV (+ (valV-v s1) (valV-v s2)))
  )

(define (valV- s1 s2)
  (valV (- (valV-v s1) (valV-v s2)))
  )

;strict -> Val (valV/closureV/promiseV) -> Val(Valv/closureV)
;destructor de promesas o cumplidor de promesas
(define (strict val)
  (match val
    [(promiseV expr env cache)
     (if (unbox cache)
         (begin
           (printf "using cache value ~n")
           (unbox cache)
           )
         (let ([interp-val (strict (interp expr env))])
           (begin (set-box! cache interp-val)
                  (printf "Forcing: ~a~n: " interp-val)
                  interp-val))
         )]
    [else val]
    )
  )


; run: Src list<fundef>? -> Expr
; corre un programa
(define (run prog)
  (let ([res (interp (parse prog) empty-env)])
    ;Un posible solucion
    ;interp env ...
    (match (strict res)
      [(valV v) v]
      [(closureV arg body env) res]
      ))
  )

(test (run '{!= 5 3}) #t)
(test (run '{== 5 5}) #t)
(test (run '{== 5 2}) #f)
(test (run '{- 5 1}) 4)
(test (run '{+ 5 1}) 6)
(test (run '{* 5 1}) 5)
(test (run '{/ 8 2}) 4)
(test (run '{and 8 2}) 2)
(test (run '{or 8 2}) 8)

(test (run '{if-tf #t {+ 1 1} {- 1 1}}) 2)
(test (run '{if-tf #f {+ 1 1} {- 1 1}}) 0)
(test (run '{if-tf {+ 2 3} #t #f}) #t)


(test (run '{with {x 3} 2}) 2)
(test (run '{with {x 3} x}) 3)
(test (run '{with {x 3} {with {y 4} x}}) 3)
(test (run '{with {x 3} {+ x 4}}) 7)
(test (run '{with {x 3} {with {x 10} {+ x x}}}) 20)
(test (run '{with {x 3} {with {x x} {+ x x}}}) 6)
(test (run '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (run '{with {x 3} {+ 1 {with {y 2} {+ x y}}}}) 6)
(test (run '{with {x 3} {with {y {+ 2 x}} {+ x y}}}) 8)
(test (run '{with {x 3} {if-tf {+ x 1} {+ x 3} {+ x 9}}}) 6)

(run '{with {z {+ 2 2}}
              {with {y {+ z z}}
                    {with {x {+ y y}}
                          {+ x x}}}})

(constant-folding (parse '{with {x {+ 1 2 {* 3 4}}} {+ 1 x}}))

(test (constant-folding (parse '{with {x {+ 1 2 {* 3 4}}} {+ 1 x}}))
      (parse '{with {x 15} {+ 1 x}}))
(test (constant-folding (parse '{with {x {+ y 2 {* 3 4}}} {+ 1 x}}))
      (parse '{with {x {+ y 2 12}} {+ 1 x}}))
(test (constant-folding (parse '{if-tf {< x 1} {+ 3 3} {+ 5 9}}))
      (parse '{if-tf {< x 1} 6 14}))
(test (constant-folding (parse'{{fun {x} {+ x {* 2 4}}} {+ 5 5}}))
      (parse '{{fun {x} {+ x 8}} 10}))


(test (constant-propagation
   (parse '{with {x 3} {+ x x}})) (parse '{with {x 3} {+ 3 3}}))
(test (constant-propagation
   (parse '{with {x 3} {with {y 5} {+ x y}}})) (parse '{with {x 3} {with {y 5} {+ 3 5}}}))
(test (constant-propagation
   (parse '{with {x 3} {with {y 5} {+ z z}}})) (parse '{with {x 3} {with {y 5} {+ z z}}}))

;(run '{string "Hello, " "World!"}) "Hello, World!"

#|

(test/exn (run '{f 10}) "undefined function")
(test (run '{f 10} (list '{define {f x} {+ x x}})) 20)
(test (run '{add1 {add1 {add1 10}}} (list '{define {add1 x} {+ x 1}})) 13)
(run '{f 10} (list '{define {add1 x} {+ x 1}}'{define {f x} {+ {add1 x} {add1 x}}}))


;(run '{f 10} (list '{define {f x} {f x}}))

;(test (run env-lookup 'y (('x 1 ('y 4 (mtEnv))))) 4) corregir este test

;(run '{with {n 5} {f 10}})

|#