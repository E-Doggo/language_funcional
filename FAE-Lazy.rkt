#lang play
(print-only-errors #f) ; Para ver solo los errores.

#|
<FAE-L> ::=   <num> | <bool> | <id>
            | (+ <FAE> <FAE>)
            | (- <FAE> <FAE>)
            | (if-tf <FAE> <FAE> <FAE>)
            | (with <id> <FAE> <FAE>)
            | (app <FAE> <FAE>) ; puedo aplicar una funcion a otra funcion / puedo usar una funcion como argumento. 
            | (fun <id> <FAE>) ; fun(que es una lambda) nombre-arg body
|#

; Ejemplos de uso de una funcion como valor
; {fun {x} {+ x 1}}
; {{fun {x} {+ x 1}} 10} --> 11
; {with {apply10 {fun {f} {f 10}}} {apply10 add1}}
; {{addN 10} 20}

(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [add l r]                               ; (+ <FAE> <FAE>)
  [sub l r]                               ; (- <FAE> <FAE>)
  [if-tf c et ef]                         ; (if-tf <FAE> <FAE> <FAE>)
; [with id-name named-expr body-expr]     ; (with <id> <FAE> <FAE>) "syntax sugar"
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <FAE> <FAE>) ; ahora podemos aplicar una funcion a otra
  [fun arg body]   
) 


#|


withN( (n 2) (m 3) (p 4) (+ n m p))
(with (n 2) (with (m 3) (with (p 4) (+ n m p)))))
|#

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
; buscar el valor de una variable dentro del ambiete
(define (env-lookup x env)
  (match env
    [(mtEnv) (error "undefined: " x)]
    [(aEnv id val tail)(if (eq? id x) val (env-lookup x tail))]
    )
  )

; parse: Src -> Expr
; parsea codigo fuente
(define (parse src)
  (match src
    [(? number?) (num src)]
    [(? boolean?) (bool src)]
    [(? symbol?) (id src)]
    [(list '+ s1 s2) (add (parse s1) (parse s2))]
    [(list '- s1 s2) (sub (parse s1) (parse s2))]
    ;[(add )]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (list x e) b) (app (fun x (parse b)) (parse e))]
    [(list arg e) (app  (parse arg) (parse e))]
    [(list 'fun args body) (parse-fun args body)]
    ;[(fun arg body) body]
    )
  )

(define (parse-fun args body)
  (cond
    [(null? args) (fun '() (parse body))]
    [(list? args) (match args
                    [(list arg) (fun arg (parse body))]
                    [(cons h t) (parse(fun h (parse-fun t body)))])]
    )
  )

(deftype Val
  (valV v) ; numero, booleano, string, byte, etc.
  (closureV arg body env) ; closure = fun + env
  (promiseV expr env) ; promise = expr-L + env
  )

; interp :: Expr  Env -> Val
; interpreta una expresion
(define (interp expr env)
  (match expr
    [(num n) (valV n)]
    [(bool b) (valV b)]
    [(id x) (env-lookup x env)]; buscar el valor de x en env
    [(add l r) (valV+ (strict (interp l env)) (strict (interp r env)))]
    [(sub l r) (valV- (strict (interp l env)) (strict (interp r env)))]
    [(if-tf c et ef) (if (interp c env)
                         (interp et env)
                         (interp ef env))]
    ;[(with x e b) (interp b (extend-env x (interp e env) env))] ; Si asociamos una funcion a una variable, la funcion entra al env
    [(fun arg body) (closureV arg body env)] ; Por ahora, devolvemos la misma expresion que nos llego
    [(app f e)
     (def (closureV arg body fenv) (strict (interp f env))) ; Esto permite encontrar (fun 'x (add (id 'x) (id 'x))) por ejemplo y tomar arg y body
    
     (interp body (extend-env arg
                              (promiseV e env) ; lazy eval
                              ;(interp e env) ; eager eval
                              fenv)) ; parece que no funciona ni con estatico ni dinamico
     ]
))

; valV+ : Val -> Val
(define (valV+ s1 s2)
  (valV (+ (valV-v s1) (valV-v s2)))
  )

(define (valV- s1 s2)
  (valV (- (valV-v s1) (valV-v s2)))
  )

; strict -> Val(valV/closureV/promiseV) -> Val (valV/closureV))
; destructor de promesas - cumplidor de promesas
(define (strict val)
  (match val
    [(promiseV e env) (strict (interp e env))]
    [else val]
    )
  )

; run: Src -> Src
; corre un programa
(define (run prog)
  (let ([res (interp (parse prog) empty-env)])
    ; (interp res ...)
    (match (strict res)
      [(valV v) v]
      [(closureV arg body env) res])
    
      ;[(promiseV e env) (interp e env)])
    )
  )

(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)

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


; Adaptando las pruebas previas
;(test/exn (run '{f 10}) "undefined function") - el error partia de fundef-lookup
(test/exn (run '{f 10}) "undefined")

;(test (run '{f 10} (list '{define {f x} {+ x x}})) 20)
; 1. Asociar la funcion a un identificador
(test (run '{with {f {fun {x} {+ x x}}}{f 10}}) 20)
; 2. Usar la funcion directamente, como un lambda
(test (run '{{fun {x} {+ x x}} 10}) 20)

;(test (run '{add1 {add1 {add1 10}}}(list '{define {add1 x} {+ x 1}})) 13)
(test (run '{with {add1 {fun {x} {+ x 1}}}{add1 {add1 {add1 10}}}}) 13)


; Prueba fallida
(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {x} {+ {add1 x} {add1 x}}}}
                        {foo 10}}}) 22)

(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {f} {+ {f 10} {f 10}}}}
                        {foo add1}}}) 22)


; Pruebas para casos basicos
(test (run '{{fun {x}{+ x 1}} {+ 2 3}}) 6)
(test (run '{with {apply10 {fun {f} {f 10}}}
                  {with {add1 {fun {x} {+ x 1}}}
                        {apply10 add1}}}) 11)

#|
Sin embargo, la currificacion falla en la implementacion actual.


|#

(test (run '{with {addN {fun {n}
                       {fun {x} {+ x n}}}}
            {{addN 10} 20}}) 30)

; Tests para laziness
(test (run '{with {x y} 1}) 1)

; Tests para comprombar eval strict
(test (run '{with {x 3} {with {y x} y}}) 3)
(test (run '{with {x 3} {with {y {+ x x}} y}}) 6)

(test (run '{{fun (a) {+ a 2}} 3}) 5)

(test (run '{with {addN {fun {n}
                   {fun {x} {+ x n}}}}
        {{addN 10} 20}}) 30)


(test (run '{{fun (a b) {+ a b}} {3 2}}) 5)
(test (run '{{fun (a b c) {+ a {- b c}}} {3 2 1}}) 4)
(run '{{fun (a b) {+ a b}} {3 2}})

(run '{with {addN {fun {a}
                       {fun {b} {+ a b}}}}
            {{addN 2} 1}})

(run '{{{fun {a} {fun {b} {+ a b}}} 2} 1})







