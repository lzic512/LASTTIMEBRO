#lang racket
(provide (all-defined-out))
(require "ast.rkt" "types.rkt" "compile-ops.rkt" a86/ast)

;; Registers used
(define rax 'rax) ; return
(define rbx 'rbx) ; heap
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg
(define r15 'r15) ; stack pad (non-volatile)

;; type CEnv = (Listof [Maybe Id])
  
;; Prog -> Asm
(define (compile p)
  (match p
    [(Prog ds e)
     (prog (externs)
           (Global 'entry)
           (Label 'entry)
           (Push rbx)    ; save callee-saved register
           (Push r15)
           (Mov rbx rdi) ; recv heap pointer
           (compile-e e '())
	   checking-vector
           (Pop r15)     ; restore callee-save register
           (Pop rbx)
           (Ret)
           (compile-defines ds)
           (Label 'raise_error_align)
           pad-stack
           (Call 'raise_error))]))

(define checking-vector
    (seq (Global 'l1)
    (Global 'l2)
    (Push rax)
    (And rax type-values)
    (Cmp rax type-values)
    (Pop rax)
    (Je 'l1)
    (Mov r8 1)
    (Mov (Offset rbx 0) r8)   
    (Mov (Offset rbx 8) rax)  
    (Mov rax rbx)
    (Jmp 'l2)
    (Label 'l1)
    (Xor rax type-values)
    (Label 'l2)))

(define (compile-values es c)
      (let ((loop1  (gensym))
            (done1  (gensym))
            (empty1 (gensym))
            (empty2 (gensym))
	    (done   (gensym)))
	    (seq (Mov r8 (length es))
	         (Cmp r8 0)
	         (Je empty1)
	         (Cmp r8 1)
	         (Je empty2)
	         (Mov 'r12 r8)
	         (compile-es (reverse es) c)
         	 (Mov r8 'r12)
                 (Mov r9 rbx)
                 (Or r9 type-values)
                 (Mov (Offset rbx 0) r8)
                 (Add rbx 8)
                 (Label loop1)
                 (Pop rax)
                 (Mov (Offset rbx 0) rax)
                 (Add rbx 8)
                 (Sub r8 1)
                 (Cmp r8 0)
                 (Jne loop1)							        					         (Mov rax r9)							
		 (Jmp done1)													         (Label empty2)													         (compile-es es c)																					       	       
		 (Pop rax)
		 (Jmp done)
			
		 (Label empty1)
		
		 (Or rbx type-values)
		
		 (Mov (Offset rbx 8) r8)
		 (Mov rax rbx)										
		 (Label done1)																			
		 (Mov 'r12 (length es))						
		 (Label done)	
		 )))

(define (compile-letvals xs e el c)
      (let ((zero  (gensym))
	    (done  (gensym))
	    (loop  (gensym))
            (done2 (gensym))
	    (done3 (gensym)))
	    (seq 
	    (compile-e e c)
            (Push rax)
            (And rax type-values)
      	    (Cmp rax type-values)	
	    (Pop rax)
	
	    (Jne done2)
	
	    (assert-values rax)
	
	    (Xor rax type-values)
	
	    (Cmp rax 0)
	
	    (Jl 'raise_error)
	
	    (Je zero)               ; rax = pointer
	
	    (Mov 'r9 (Offset rax 0)) ; r9 is length
	
	    (Cmp 'r9 (length xs))
	
	    (Jne 'raise_error)
	
	    (Push 'r9)
	
	    (Mov 'r8 'r9)             ; r8 = index
	
	    (Sar 'r8 int-shift)
	
	    (Pop 'r11)               ; r11 = length
						
	    (Mov 'r10 0)
	
	    (Add rax r8)
	
	    (Mov 'r8 0)
	
	    (Label loop)
	
	    (Cmp 'r11 'r10)
	
	    (Je done)
	
	    (Mov 'r8 (Offset rax 8))
	
	    (Add rax 8)
	
	    (Push 'r8)
	
	    (Add 'r10 1)
	
	    (Jmp loop)							
	    (Label zero)
		
	    (Cmp rax (length xs))
	
	    (Jne 'raise_error)
	
	    (compile-e el (append (reverse xs) c))
	
	    (Jmp done3)
	
	    (Label done)
	
	    (compile-e el (append (reverse xs) c))
	
	    (Add rsp (* 8 (length xs)))
	
	    (Jmp done3)
	
	    (Label done2)
	
	    (Mov 'r8 (length xs))
	
	    (Cmp 'r8 1)
	
	    (Jne 'raise_error)
	
	    (Push rax)
	
	    (compile-e el (append (reverse xs) c))
	
	    (Add rsp (* 8 (length xs)))
	
	    (Label done3)									
	    )))

(define (externs)
  (seq (Extern 'peek_byte)
       (Extern 'read_byte)
       (Extern 'write_byte)
       (Extern 'raise_error)))

;; [Listof Defn] -> Asm
(define (compile-defines ds)
  (match ds
    ['() (seq)]
    [(cons d ds)
     (seq (compile-define d)
          (compile-defines ds))]))

;; Defn -> Asm
(define (compile-define d)
  (match d
    [(Defn f xs e)
     (seq (Label (symbol->label f))
          (compile-e e (reverse xs))
          (Add rsp (* 8 (length xs))) ; pop args
          (Ret))]))

;; Expr CEnv -> Asm
(define (compile-e e c)
  (match e
    [(Int i)            (compile-value i)]
    [(Bool b)           (compile-value b)]
    [(Char c)           (compile-value c)]
    [(Eof)              (compile-value eof)]
    [(Empty)            (compile-value '())]
    [(Var x)            (compile-variable x c)]
    [(Str s)            (compile-string s)]
    [(Prim0 p)          (compile-prim0 p c)]
    [(Prim1 p e)        (compile-prim1 p e c)]
    [(Prim2 p e1 e2)    (compile-prim2 p e1 e2 c)]
    [(Prim3 p e1 e2 e3) (compile-prim3 p e1 e2 e3 c)]
    [(If e1 e2 e3)      (compile-if e1 e2 e3 c)]
    [(Begin e1 e2)      (compile-begin e1 e2 c)]
    [(Let x e1 e2)      (compile-let x e1 e2 c)]
     [(Values es)          (compile-values es c)]
         [(Let-values xs e el) (compile-letvals xs e el c)]
    [(App f es)         (compile-app f es c)]))

;; Value -> Asm
(define (compile-value v)
  (seq (Mov rax (value->bits v))))

;; Id CEnv -> Asm
(define (compile-variable x c)
  (let ((i (lookup x c)))
    (seq (Mov rax (Offset rsp i)))))

;; String -> Asm
(define (compile-string s)
  (let ((len (string-length s)))
    (if (zero? len)
        (seq (Mov rax type-str))
        (seq (Mov rax len)
             (Mov (Offset rbx 0) rax)
             (compile-string-chars (string->list s) 8)
             (Mov rax rbx)
             (Or rax type-str)
             (Add rbx
                  (+ 8 (* 4 (if (odd? len) (add1 len) len))))))))

;; [Listof Char] Integer -> Asm
(define (compile-string-chars cs i)
  (match cs
    ['() (seq)]
    [(cons c cs)
     (seq (Mov rax (char->integer c))
          (Mov (Offset rbx i) 'eax)
          (compile-string-chars cs (+ 4 i)))]))

;; Op0 CEnv -> Asm
(define (compile-prim0 p c)
  (compile-op0 p))

;; Op1 Expr CEnv -> Asm
(define (compile-prim1 p e c)
  (seq (compile-e e c)
       (compile-op1 p)))

;; Op2 Expr Expr CEnv -> Asm
(define (compile-prim2 p e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (compile-op2 p)))

;; Op3 Expr Expr Expr CEnv -> Asm
(define (compile-prim3 p e1 e2 e3 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (Push rax)
       (compile-e e3 (cons #f (cons #f c)))
       (compile-op3 p)))

;; Expr Expr Expr CEnv -> Asm
(define (compile-if e1 e2 e3 c)
  (let ((l1 (gensym 'if))
        (l2 (gensym 'if)))
    (seq (compile-e e1 c)
         (Cmp rax (value->bits #f))
         (Je l1)
         (compile-e e2 c)
         (Jmp l2)
         (Label l1)
         (compile-e e3 c)
         (Label l2))))

;; Expr Expr CEnv -> Asm
(define (compile-begin e1 e2 c)
  (seq (compile-e e1 c)
       (compile-e e2 c)))

;; Id Expr Expr CEnv -> Asm
(define (compile-let x e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons x c))
       (Add rsp 8)))

;; Id [Listof Expr] CEnv -> Asm
;; The return address is placed above the arguments, so callee pops
;; arguments and return address is next frame
(define (compile-app f es c)
  (let ((r (gensym 'ret)))
    (seq (Lea rax r)
         (Push rax)
         (compile-es es (cons #f c))
         (Jmp (symbol->label f))
         (Label r))))

;; [Listof Expr] CEnv -> Asm
(define (compile-es es c)
  (match es
    ['() '()]
    [(cons e es)
     (seq (compile-e e c)
          (Push rax)
          (compile-es es (cons #f c)))]))

;; Id CEnv -> Integer
(define (lookup x cenv)
  (match cenv
    ['() (error "undefined variable:" x)]
    [(cons y rest)
     (match (eq? x y)
       [#t 0]
       [#f (+ 8 (lookup x rest))])]))

;; Symbol -> Label
;; Produce a symbol that is a valid Nasm label
(define (symbol->label s)
  (string->symbol
   (string-append
    "label_"
    (list->string
     (map (λ (c)
            (if (or (char<=? #\a c #\z)
                    (char<=? #\A c #\Z)
                    (char<=? #\0 c #\9)
                    (memq c '(#\_ #\$ #\# #\@ #\~ #\. #\?)))
                c
                #\_))
         (string->list (symbol->string s))))
    "_"
    (number->string (eq-hash-code s) 16))))
