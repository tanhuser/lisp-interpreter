(def else '#t)

(def list (fn args args))

(def atom? (fn (x) (not (list? x))))

(def splice-body (fn (body) (cond ((atom? body) body)
                                   ((= (tail body) '()) (head body))
                                   (else (cons do body)))))

(def defmacro (macro (name args & body) (list 'def name (list 'macro args (splice-body body)))))

(defmacro defun (name args & body)
	(list 'def name (list 'fn args (splice-body body))))  

(defun null? (l)
  (= l '()))

(defmacro if (c t & e)
  (cond ((null? e) (list 'cond (list c t)))
        (else (list 'cond (list c t) (list 'else (head e))))))

(defun map (f lst) 
  (if (null? lst)
       lst
       (cons (f (head lst)) (map f (tail lst)))))

(defmacro let (binds & body)
  (cons (list 'fn (map head binds) (splice-body body)) (map snd binds)))      

(def fst head)

(defun snd (l)
  (head (tail l)))

(defun fold (f s l)
  (if (null? l)
      s
      (fold f (f s (head l)) (tail l))))

(defun fold1 (f l)
  (fold f (head l) (tail l)))

(defun any? (p l)
  (fold1 or (map p l)))

(defun append (l1 l2)
  (if (null? l1)
      l2
      (cons (head l1) (append (tail l1) l2))))

(defmacro quasiquote (e)
  (qq-expand e))

(defun qq-expand (x)
  (if (list? x)
      (cond ((null? x) (list 'quote '()))
	    ((= (head x) 'unquote) (snd x))
	    ((= (head x) 'quasiquote) (qq-expand (qq-expand (snd x))))
	    (else (list 'append 
		    (qq-expand-list (head x))
		    (qq-expand (tail x)))))
      (list 'quote x)))

(defun qq-expand-list (x)
   (if (list? x)
      (cond ((null? x) (list 'quote (list '())))
	    ((= (head x) 'unquote) (list 'list (snd x)))
	    ((= (head x) 'unquote-splicing) (snd x))
	    ((= (head x) 'quasiquote) (qq-expand-list (qq-expand (snd x))))
	    (else 
	     (list 'list (list 'append 
		    (qq-expand-list (head x))
		    (qq-expand (tail x))))))
(list 'quote (list x))))

(defun zip l
  (if (any? null? l)
      '()
       (cons (map head l) (apply zip (map tail l)))))
