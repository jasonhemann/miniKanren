;; Recently improved by Jason Hemann and Dan Friedman

;; The code of this system comprises two steps.  The first step is to run
;; a goal and check if the result fails to make sense: we term this
;; "fast fail".  If each goal goes to completion, then we have the reify
;; step.  The work of the reify step is to take the final state of the
;; computation and return a Scheme value.  This also comprises two steps.
;; The first step is to try every funtion in a cycle of functions that try
;; to make a new state, which is then fed to the next function in the cycle.
;; Each cycle function takes a state and returns a state: it cannot fail.
;; When one of the functions does not improve the state, it becomes the
;; function to reach without ever changing the state by the intervening
;; functions.  When no improvements can be made we have found a fixed point.
;; Each of these intervening cycle functions tried to change the state, but
;; couldn't.  Next we turn the value along with the non-empty fields of the
;; state into a list structure.  Reification does not appear to be a
;; bottleneck, since it is just turning an answer into something readable.
;; There may be many answers, and each answer has to be reified.

;; We have just added not-pairo to the system.  It appears to be working
;; and passes our test cases. It's field is called A.

(define rhs
  (lambda (pr)
    (cdr pr)))
 
(define lhs
  (lambda (pr)
    (car pr)))

(define-syntax case-value
  (syntax-rules ()
    ((_ u ((t1) e0) ((at dt) e1) ((t2) e2))
     (let ((t u))
       (cond
	 ((var? t) (let ((t1 t)) e0))
	 ((pair? t) (let ((at (car t)) (dt (cdr t))) e1))
	 (else (let ((t2 t)) e2)))))))

(define var
  (lambda (dummy)
    (vector dummy)))
 
(define var?
  (lambda (x)
    (vector? x)))

(define walk
  (lambda (u H)
    (cond
      ((and (var? u) (assq u H)) =>
       (lambda (pr) (walk (rhs pr) H)))
      (else u))))

(define unify
  (lambda (u v H)
    (let ((u (walk u H))
          (v (walk v H)))
      (cond
        ((and (pair? u) (pair? v))
         (let ((H (unify (car u) (car v) H)))
           (and H
             (unify (cdr u) (cdr v) H))))
        (else (unify-nonpair u v H))))))
 
(define unify-nonpair
  (lambda (u v H)
    (cond
      ((eq? u v) H)
      ((var? u) (ext-H-check u v H))
      ((var? v) (ext-H-check v u H))
      ((equal? u v) H)
      (else #f))))

(define ext-H-check
  (lambda (x v H)
    (case-value v
      ((v) (ext-H x v H))
      ((au du) (cond
                 ((occurs-check x v H) #f)
                 (else (ext-H x v H))))
      ((v) (ext-H x v H)))))
 
(define ext-H
  (lambda (x v H)
    (cons `(,x . ,v) H)))
     
(define occurs-check
  (lambda (x v H)
    (case-value (walk v H)
      ((v) (eq? v x))
      ((av dv)
       (or (occurs-check x av H)
           (occurs-check x dv H)))
      ((v) #f))))

(define prefix-H
  (lambda (H0 H)
    (cond
      ((eq? H0 H) '())
      (else (cons (car H0)
              (prefix-H (cdr H0) H))))))

(define walk*
  (lambda (v H)
    (case-value (walk v H)
      ((v) v)
      ((av dv)
       (cons (walk* av H) (walk* dv H)))
      ((v) v))))

(define reify-R
  (lambda (v R)
    (case-value (walk v R)
      ((v) (let ((n (length R)))
             (let ((name (reify-name n)))
               (ext-H v name R))))
      ((av dv) (let ((R (reify-R av R)))
                 (reify-R dv R)))
      ((v) R))))

(define unify-safe
  (lambda (u v H)
    (let ((u (walk u H))
          (v (walk v H)))
      (cond
        ((and (pair? u) (pair? v))
         (let ((H (unify-safe (car u) (car v) H)))
           (and H
             (unify-safe (cdr u) (cdr v) H))))
        (else (unify-nonpair-safe u v H))))))
  
(define unify-nonpair-safe
  (lambda (u v H)
    (cond
      ((eq? u v) H)
      ((var? u) (ext-H u v H))
      ((var? v) (ext-H v u H))
      (else H))))

(define reify-name
  (lambda (n)
    (string->symbol
      (string-append "_" "." (number->string n)))))

(define reify
  (lambda (x)
    (lambda (c)
      (let ((c (cycle c)))
        (let ((H (c->H c)))
          (let ((D (walk* (c->D c) H))
                (Y (walk* (c->Y c) H)) 
                (N (walk* (c->N c) H))
                (A (walk* (c->A c) H))
                (T (walk* (c->T c) H))
                (v (walk* x H)))
            (let ((R (reify-R v '())))
              (reify+
               v R c H D Y N A T))))))))
 
(define reify+
  (lambda (v R c H D Y N A T)
    (reify++ v R
      (D-subsumed
       (remp
          (lambda (d) 
            (anyvar? (walk* d H) R))
          (drop-from-D-using-T H
            (c->Y c) (c->N c)
	    (c->A c) (c->T c)
            (rem-xx-from-D D H)))) 
      (remp (lambda (y) (anyvar? y R))
        Y)
      (remp (lambda (n) (anyvar? n R))
        N)
      (remp (lambda (a) (anyvar? a R))
        A)
      (remp (lambda (t) (anyvar? t R))
        T))))
 
(define reify++
  (lambda (v R D Y N A T)
    (form (walk* v R) (walk* D R)
          (walk* Y R) (walk* N R)
          (walk* A R) (T-subsumed (walk* T R)))))
 
(define form
  (lambda (v D Y N A T)
    (let ((fd (sort-D D))
          (fy (sorter Y))
          (fn (sorter N))
          (fa (sorter A))
          (ft (sorter T)))
      (let ((fd (if (null? fd) fd
                    (let ((fd (drop-dot-D fd)))
                      `((=/= . ,fd)))))
            (fy (if (null? fy) fy `((sym . ,fy))))
            (fn (if (null? fn) fn `((num . ,fn))))
            (fa (if (null? fa) fa `((not-pair . ,fa))))
            (ft (if (null? ft) ft
                    (let ((ft (drop-dot ft)))
                      `((absento . ,ft))))))
        (cond
          ((and (null? fd) (null? fy)
                (null? fn) (null? fa)
                (null? ft))
           v)
          (else (append `(,v) fd fa fn fy ft)))))))

(define lex<=?
  (lambda (x y)
    (cond
      ((vector? x) #t)
      ((vector? y) #f)
      ((port? x) #t)
      ((port? y) #f)
      ((procedure? x) #t)
      ((procedure? y) #f)
      ((boolean? x)
       (cond
         ((boolean? y) (or (not x) (eq? x y)))
         (else #t)))
      ((boolean? y) #f)
      ((null? x) #t)
      ((null? y) #f)
      ((char? x)
       (cond
         ((char? y) (char<=? x y))
         (else #t)))
      ((char? y) #f)
      ((number? x)
       (cond
         ((number? y) (<= x y))
         (else #t)))
      ((number? y) #f)
      ((string? x)
       (cond
         ((string? y) (string<=? x y))
         (else #t)))
      ((string? y) #f)
      ((symbol? x)
       (cond
         ((symbol? y)
          (string<=? (symbol->string x)
                     (symbol->string y)))
         (else #t)))
      ((symbol? y) #f)
      ((pair? x)
       (cond
         ((pair? y)
          (cond          
            ((equal? (car x) (car y))
             (lex<=? (cdr x) (cdr y)))
            (else (lex<=? (car x) (car y)))))))
      ((pair? y) #f)
      (else #t))))

(define sorter
  (lambda (ls)
    (list-sort lex<=? ls)))
 
(define sort-D
  (lambda (D)
    (sorter
      (map sort-d D))))
 
(define sort-d
  (lambda (d)
    (list-sort
      (lambda (x y)
        (lex<=? (car x) (car y)))
      (map sort-pr d))))
 
(define drop-dot
  (lambda (X)
    (map (lambda (t)
           (let ((a (lhs t))
                 (d (rhs t)))
             `(,a ,d)))
         X)))
          
(define datum->string
  (lambda (x)
    (call-with-string-output-port
      (lambda (p) (display x p)))))         
 
(define drop-dot-D
  (lambda (D)
    (map drop-dot D)))
 
(define lex<-reified-name?
  (lambda (r)
    (char<?
      (string-ref (datum->string r) 0)
      (string-ref "_" 0))))
               
(define sort-pr
  (lambda (pr)
    (let ((l (lhs pr))
          (r (rhs pr)))
      (cond
        ((lex<-reified-name? r) pr)
        ((lex<=? r l) `(,r . ,l))
        (else pr)))))

(define rem-xx-from-D
  (lambda (D H)
    (remp not
      (map (lambda (d)
             (let ((d-l (lhs d))
                   (d-r (rhs d)))
	       (let ((H0 (unify-safe d-l d-r H)))
		 (prefix-H H0 H))))
        D))))
            
(define anyvar?
  (lambda (u H)
    (case-value u
      ((u) (var? (walk u H)))
      ((au du) (or (anyvar? au H)
                   (anyvar? du H)))
      ((u) #f))))

(define drop-from-D-using-T
  (lambda (H Y N A T D)
    (remp (lambda (d)
	    (exists
	      (T-superfluous-pr? H Y N A T)
	      d))
	  D)))
 
(define T-superfluous-pr?
  (lambda (H Y N A T)
    (lambda (pr)
      (let ((pr-a (walk (lhs pr) H))
            (pr-d (walk (rhs pr) H)))
        (cond
          ((exists
             (lambda (t)
               (let ((t-a (walk (lhs t) H))
                     (t-d (walk (rhs t) H)))
                 (terms-pairwise=?
                   pr-a pr-d t-a t-d H)))
             T)
           (for-all
             (stays-in-T? H Y N A pr-a pr-d)
             T))
          (else #f))))))

(define stays-in-T?
  (lambda (H Y N A pr-a pr-d)
    (lambda (t)
      (let ((t-a (walk (lhs t) H))
            (t-d (walk (rhs t) H)))
        (or
          (not
            (terms-pairwise=?
              pr-a pr-d t-a t-d H))
          (untyped-var? H Y N A t-d)
          (pair? t-d))))))
     
(define terms-pairwise=?
  (lambda (pr-a pr-d t-a t-d H)
    (or (and (term=? pr-a t-a H)
             (term=? pr-d t-a H))
        (and (term=? pr-a t-d H)
             (term=? pr-d t-a H)))))            

(define D-subsumed
  (lambda (D)
    (let D-subsumed ((D D) (D0 '()))
      (cond
        ((null? D) D0)
        ((or (D-subsumed? (car D) (cdr D))
             (D-subsumed? (car D) D0))
         (D-subsumed (cdr D) D0))
        (else (D-subsumed (cdr D)
                (cons (car D) D0)))))))
 
(define D-subsumed?
  (lambda (d D0)
    (cond
      ((null? D0) #f)
      (else
       (let ((d^ (unify* (car D0) d)))
         (or (and d^ (eq? d^ d))
             (D-subsumed? d (cdr D0))))))))
 
(define unify*
  (lambda (d H)
    (unify (map lhs d) (map rhs d) H)))
 
(define unify*-safe
  (lambda (d H)
    (unify-safe
      (map lhs d)
      (map rhs d)
      H)))

(define T-subsumed
  (lambda (T)
    (let T-subsumed ((T T) (T0 '()))
      (cond
        ((null? T) T0)
        (else
         (let ((l (lhs (car T)))
               (r (rhs (car T))))
           (cond
             ((or
                (T-subsumed? l r (cdr T))
                (T-subsumed? l r T0))
              (T-subsumed (cdr T) T0))
             (else
              (T-subsumed (cdr T)
                (cons (car T) T0))))))))))
 
(define T-subsumed? 
  (lambda (l r T)
    (cond
      ((null? T) #f)
      (else
       (let ((l^ (lhs (car T)))
             (r^ (rhs (car T))))
         (or
           (and (eq? r r^) (member* l^ l))
           (T-subsumed? l r (cdr T))))))))
 
(define member*
  (lambda (x u)
    (cond
      ((eq? x u) #t)
      ((pair? u)
       (or (member* x (car u))
           (member* x (cdr u))))
      (else #f))))    

(define-syntax lambdag@
  (syntax-rules (:)
    ((_ (c) e) (lambda (c) e))
    ((_ (c : H D Y N A T) e)
     (lambda (c)
       (let ((H (c->H c)) (D (c->D c))
             (Y (c->Y c)) (N (c->N c))
             (A (c->A c)) (T (c->T c)))
         e)))))
          
(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))
 
(define mzero (lambda () #f))
(define unit (lambdag@ (c) c))
(define choice (lambda (c f) (cons c f)))
(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))
(define empty-f (lambdaf@ () (mzero)))
(define State
  (lambda (H D Y N A T)
    `(,H ,D ,Y ,N ,A ,T)))
(define empty-c '(() () () () () ()))
         
          
(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((c^) e2) ((c f) e3))
     (let ((c-inf e))
       (cond
         ((not c-inf) e0)
         ((procedure? c-inf)  (let ((f^ c-inf)) e1))
         ((not (and (pair? c-inf)
                 (procedure? (cdr c-inf))))
          (let ((c^ c-inf)) e2))
         (else (let ((c (car c-inf)) (f (cdr c-inf))) 
                 e3)))))))
 
(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (c)
       (inc
         (let ((x (var 'x)) ...)
           (bind* (g0 c) g ...)))))))
 
(define bind
  (lambda (c-inf g)
    (case-inf c-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((c) (g c))
      ((c f) (mplus (g c) (lambdaf@ () (bind (f) g)))))))                 

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (take n
       (lambdaf@ ()
         ((fresh (x) g0 g ...
            (lambdag@ (final-c)
              (let ((z ((reify x) final-c)))
                (choice z empty-f))))
          empty-c))))))
 
(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))
 
(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else
       (case-inf (f) 
         (() '())
         ((f) (take n f))
         ((c) (cons c '()))
         ((c f) (cons c
                  (take (and n (- n 1)) f))))))))
 
(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c) 
       (inc 
         (mplus* 
           (bind* (g0 c) g ...)
           (bind* (g1 c) g^ ...) ...))))))
 
(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0 
                    (lambdaf@ () (mplus* e ...))))))
 
(define mplus
  (lambda (c-inf f)
    (case-inf c-inf
      (() (f))
      ((f^) (inc (mplus (f) f^)))
      ((c) (choice c f))
      ((c f^) (choice c (lambdaf@ () (mplus (f) f^)))))))
 
(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))          

(define c->H (lambda (c) (car c)))
(define c->D (lambda (c) (cadr c)))
(define c->Y (lambda (c) (caddr c)))
(define c->N (lambda (c) (cadddr c)))
(define c->A (lambda (c) (cadddr (cdr c))))
(define c->T (lambda (c) (cadddr (cddr c))))
 
(define absento
  (lambda (u v)
    (lambdag@ (c : H D Y N A T)
      (cond
        ((mem-check u v H) (mzero))
        (else
         (unit (State H D Y N A `((,u . ,v) . ,T))))))))
 
(define mem-check
  (lambda (u t H)
    (let ((t (walk t H)))
      (cond
        ((pair? t)
         (or (term=? u t H)
             (mem-check u (car t) H)
             (mem-check u (cdr t) H)))
        (else (term=? u t H))))))

(define term=?
  (lambda (u v H)
    (let ((u (walk u H))
          (v (walk v H)))
      (cond
        ((and (pair? u) (pair? v))
         (and (term=? (car u) (car v) H)
              (term=? (cdr u) (cdr v) H)))
        (else (term=?-nonpair u v H))))))

(define term=?-nonpair
  (lambda (u v H)
    (cond
      ((eq? u v) #t)
      ((var? u) #f)
      ((var? v) #f)
      ((equal? u v) #t)
      (else #f))))

(define ground-non-type?
  (lambda (pred)
    (lambda (u H)
      (let ((u (walk u H)))
        (cond
          ((var? u) #f)
          (else (not (pred u))))))))
     
(define ground-non-symbol?
  (ground-non-type? symbol?))      
 
(define ground-non-number?
  (ground-non-type? number?))

(define not-pair? (lambda (x) (not (pair? x))))

(define ground-pair?
  (ground-non-type? not-pair?))
 
(define symbolo
  (lambda (u)
    (lambdag@ (c : H D Y N A T)
      (cond
        ((ground-non-symbol? u H) (mzero))
        ((mem-check u N H) (mzero))
        (else (unit (State H D `(,u . ,Y) N A T)))))))
 
(define numbero 
  (lambda (u)
    (lambdag@ (c : H D Y N A T)
      (cond
        ((ground-non-number? u H) (mzero))
        ((mem-check u Y H) (mzero))
        (else (unit (State H D Y `(,u . ,N) A T)))))))

(define not-pairo
  (lambda (u)
    (lambdag@ (c : H D Y N A T)
      (cond
        ((ground-pair? u H) (mzero))
        (else (unit (State H D Y N `(,u . ,A) T)))))))

(define =/=
  (lambda (u v)
    (lambdag@ (c : H D Y N A T)
      (cond
        ((unify u v H) =>
         (lambda (H0)
           (cond
             ((eq? H0 H) (mzero))
             (else
              (let ((d `(,u . ,v)))
                (unit
                  (State H `(,d . ,D) Y N A T)))))))
        (else c)))))    
 
(define ==
  (lambda (u v)
    (lambdag@ (c : H D Y N A T)
      (cond
        ((unify u v H) =>
         (lambda (H0)
           (cond
             ((eq? H0 H) (unit c))
             (else
              (cond
                ((==fail-check H0 D Y N A T)
                 (mzero))
                (else
                 (unit (State H0 D Y N A T))))))))
        (else (mzero))))))
 
(define ==fail-check
  (lambda (H0 D Y N A T)  
    (or (atomic-fail-check H0 Y ground-non-symbol?)
        (atomic-fail-check H0 N ground-non-number?)
        (atomic-fail-check H0 A ground-pair?)        
        (symbolo-numbero-fail-check H0 Y N)
        (=/=-fail-check H0 D)
        (absento-fail-check H0 T))))

(define atomic-fail-check
  (lambda (H A pred)
    (exists
      (lambda (a)
        (pred (walk a H) H))
      A)))
 
(define symbolo-numbero-fail-check 
  (lambda (H Y N)
    (let ((N (map (lambda (n) (walk n H)) N)))    
      (exists
        (lambda (y)
          (exists (same-var? (walk y H)) N))
        Y))))
 
(define absento-fail-check
  (lambda (H T)
    (exists
      (lambda (t) (mem-check (lhs t) (rhs t) H))
      T)))
 
(define =/=-fail-check
  (lambda (H D)
    (exists
      (lambda (d) (term=? (lhs d) (rhs d) H))
      D)))
 
(define tagged?
  (lambda (H Y y^)
    (exists (lambda (y) (eqv? (walk y H) y^)) Y)))
 
(define untyped-var?
  (lambda (H Y N A t)
    (let ((in-type? (lambda (y)
                      (eq? (walk y H) t))))
      (and (var? t)
           (not (exists in-type? Y))
           (not (exists in-type? N))
           (not (exists in-type? A))))))
 
(define const?
  (lambda (H)
    (lambda (a)
      (not (var? (walk a H))))))
 
(define drop-from-N-b/c-const
  (lambdag@ (c : H D Y N A T)
    (cond
      ((find (const? H) N) =>
       (lambda (n)
         (State H D Y (remq1 n N) A T)))
      (else c))))
 
(define drop-from-Y-b/c-const
  (lambdag@ (c : H D Y N A T)
    (cond
      ((find (const? H) Y) =>
       (lambda (y)
         (State H D (remq1 y Y) N A T)))
      (else c))))

(define drop-from-A-b/c-const
  (lambdag@ (c : H D Y N A T)
    (cond
      ((find (const? H) A) =>
       (lambda (a)
         (State H D Y N (remq1 a A) T)))
      ((memp (lambda (x) (not (walk x H))) A) =>
       (lambda (a*)
         (State H D Y N (remq1 (car a*) A) T)))
      (else c))))
 
(define remq1
  (lambda (elem ls)
    (cond
      ((null? ls) '())
      ((eq? (car ls) elem) (cdr ls))
      (else (cons (car ls)
              (remq1 elem (cdr ls)))))))
 
(define same-var?
  (lambda (v)
    (lambda (v^)
      (and (var? v) (var? v^) (eq? v v^)))))
 
(define find-dup
  (lambda (f H)
    (lambda (set)
      (let loop ((set set))
        (cond
          ((null? set) #f)
          (else
           (let ((e (car set)))
             (let ((e0 (walk e H)))
               (cond
                 ((find (lambda (e1)
                          ((f e0) (walk e1 H)))
                    (cdr set))
                  e)
                 (else
                  (loop (cdr set))))))))))))

(define drop-from-N-b/c-dup-var
  (lambdag@ (c : H D Y N A T)
    (cond
      (((find-dup same-var? H) N) =>
       (lambda (n)
         (State H D Y (remq1 n N) A T)))
      (else c))))
 
(define drop-from-Y-b/c-dup-var
  (lambdag@ (c : H D Y N A T)
    (cond
      (((find-dup same-var? H) Y) =>
       (lambda (y)
         (State H D (remq1 y Y) N A T)))
      (else c))))

(define drop-from-A-b/c-dup-var
  (lambdag@ (c : H D Y N A T)
    (cond
      (((find-dup same-var? H) A) =>
       (lambda (a)
         (State H D Y N (remq1 a A) T)))
      (else c))))

(define drop-var-from-A-b/c-Y
  (lambdag@ (c : H D Y N A T)
    (let ((Y (map (lambda (y) (walk y H)) Y)))
      (cond
        ((find (lambda (a)
                 (exists (same-var? (walk a H)) Y))
               A) =>
               (lambda (a)
                 (State H D Y N (remq1 a A) T)))
        (else c)))))

(define drop-var-from-A-b/c-N
  (lambdag@ (c : H D Y N A T)
    (let ((N (map (lambda (n) (walk n H)) N)))
      (cond
        ((find (lambda (a)
                 (exists (same-var? (walk a H)) N))
               A) =>
               (lambda (a)
                 (State H D Y N (remq1 a A) T)))
        (else c)))))

(define var-type-mismatch?
  (lambda (H Y N A t1 t2)
    (cond
      ((num? H N t1)
       (not (num? H N t2)))
      ((sym? H Y t1)
       (not (sym? H Y t2)))
      ((not-pr? H A t1)
       (not (not (pair? t2))))
      (else #f))))
 
(define term-ununifiable?
  (lambda (H Y N A t1 t2)
    (let ((t1 (walk t1 H))
          (t2 (walk t2 H)))
      (cond
        ((or (untyped-var? H Y N A t1)
             (untyped-var? H Y N A t2)) #f)
        ((var? t1)
         (var-type-mismatch? H Y N A t1 t2))
        ((var? t2)
         (var-type-mismatch? H Y N A t2 t1))
        ((and (pair? t1) (pair? t2))
         (or (term-ununifiable? H Y N A
               (car t1) (car t2))
             (term-ununifiable? H Y N A
               (cdr t1) (cdr t2))))
        (else (not (eqv? t1 t2)))))))  
    
(define num?
  (lambda (H N n)
    (let ((n (walk n H)))
      (cond
        ((var? n) (tagged? H N n))
        (else (number? n))))))
     
(define sym?
  (lambda (H Y y)
    (let ((y (walk y H)))          
      (cond
        ((var? y) (tagged? H Y y))
        (else (symbol? y))))))

(define not-pr?
  (lambda (H A a)
    (let ((a (walk a H)))          
      (cond
        ((var? a) (tagged? H A a))
        (else (not-pair? a))))))
          
(define drop-from-D-b/c-d1-occurs-d2
  (lambdag@ (c : H D Y N A T)
    (cond
      ((find (lambda (d)
               (tree-occurs-check (lhs d) (rhs d) H))
         D) => (lambda (d)
                 (State H (remq1 d D) Y N A T)))
      (else c))))          

(define split-t-move-to-D-b/c-pair
  (lambdag@ (c : H D Y N A T)
    (cond
      ((exists
         (lambda (t)
           (let ((tr (walk (rhs t) H)))
             (cond
               ((pair? tr)
                ((split-t-move-to-D tr t) c))
               (else #f))))
         T))
      (else c))))
 
(define split-t-move-to-D
  (lambda (tr t)
    (lambdag@ (c : H D Y N A T)
      (let ((tl (lhs t))
            (tr-a (car tr))
            (tr-d (cdr tr)))
        (let ((t1 `(,tl . ,tr-a))
              (t2 `(,tl . ,tr-d))
              (T (remq1 t T)))
          (let ((T `(,t1 . (,t2 . ,T))))
            (cond
              ((unify tl tr H) =>
               (lambda (H0)
                 (cond
                   ((eq? H0 H)
                    (State H D Y N A T))
                   (else
                     (let ((D `(,t . ,D)))
                       (State H D Y N A T))))))
              (else (State H D Y N A T))))))))) 
 
(define tree-occurs-check
  (lambda (d-a d-b H)
    (let ((d-a (walk d-a H))
          (d-b (walk d-b H)))
      (cond
        ((var? d-a)
         (occurs-check d-a d-b H))
        ((var? d-b)
         (occurs-check d-b d-a H))
        ((and (pair? d-a) (pair? d-b))
         (or
           (tree-occurs-check (car d-a) (car d-b) H)
           (tree-occurs-check (cdr d-a) (cdr d-b) H)))
        (else #f)))))

(define move-from-T-to-D-b/c-t2-A
  (lambdag@ (c : H D Y N A T)
    (cond
      ((exists
         (lambda (t)
           (let ((t2 (rhs t)))
             ((movable-t? (walk t2 H) t2 t) c)))
         T))
      (else c))))
 
(define movable-t?
  (lambda (t2^ t2 t)
    (lambdag@ (c : H D Y N A T)
      (cond
        ((and
           (not (untyped-var? H Y N A t2^))
           (not (pair? t2^)))
           (let ((T (remq1 t T)))
             (cond
               ((unify (lhs t) t2 H) =>
                (lambda (H0)
                  (cond
                    ((eq? H0 H)
                     (State H D Y N A T))
                    (else
                     (let ((D `(,t . ,D)))
                       (State H D Y N A T))))))
               (else (State H D Y N A T)))))
        (else #f)))))
 
(define drop-from-D-b/c-Y-or-N-or-A
  (lambdag@ (c : H D Y N A T)
    (cond
      ((find (lambda (d)
               (term-ununifiable? 
                 H Y N A (lhs d) (rhs d)))
        D) =>
       (lambda (d)
         (State H (remq1 d D) Y N A T)))
      (else c))))         
         
(define drop-from-T-b/c-t2-occurs-t1
  (lambdag@ (c : H D Y N A T)
    (cond
      ((find (lambda (t)
               (let ((t-a (walk (lhs t) H))
                     (t-d (walk (rhs t) H)))
                 (mem-check t-d t-a H)))
         T)
       => (lambda (t)
            (State H D Y N A (remq1 t T))))
      (else c))))         
 
(define LOF
  (list drop-from-Y-b/c-const
        drop-from-N-b/c-const
        drop-from-A-b/c-const
        drop-var-from-A-b/c-Y
        drop-var-from-A-b/c-N
        drop-from-Y-b/c-dup-var
        drop-from-N-b/c-dup-var
        drop-from-A-b/c-dup-var
        drop-from-D-b/c-Y-or-N-or-A
        drop-from-T-b/c-t2-occurs-t1
        move-from-T-to-D-b/c-t2-A
        split-t-move-to-D-b/c-pair))
 
(define len-LOF (length LOF))       
 
(define cycler
  (lambda (c n fns)
    (cond
      ((zero? n) c)
      ((null? fns) (cycler c len-LOF LOF))
      (else
       (let ((c^ ((car fns) c)))
         (cond
           ((not (eq? c^ c))             
            (cycler c^ len-LOF (cdr fns)))
           (else
            (cycler c (sub1 n) (cdr fns)))))))))
               
(define cycle
  (lambdag@ (c)
    (cycler c len-LOF LOF)))

(define-syntax conda
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c)
       (inc
         (ifa ((g0 c) g ...)
              ((g1 c) g^ ...) ...))))))
 
(define-syntax ifa
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((c-inf e))
       (case-inf c-inf
         (() (ifa b ...))
         ((f) (inc (loop (f))))
         ((a) (bind* c-inf g ...))
         ((a f) (bind* c-inf g ...)))))))

(define-syntax condu
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c)
       (inc
         (ifu ((g0 c) g ...)
              ((g1 c) g^ ...) ...))))))
 
(define-syntax ifu
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((c-inf e))
       (case-inf c-inf
         (() (ifu b ...))
         ((f) (inc (loop (f))))
         ((c) (bind* c-inf g ...))
         ((c f) (bind* (unit c) g ...)))))))

(define succeed (== #f #f))

(define fail (== #f #t))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g g* ...)
     (lambdag@ (c : H D Y N A T)
       (let ((x (walk* x H)) ...)
         ((fresh () g g* ...) c))))))

(define booleano
  (lambda (x)
    (conde
      ((== #f x) succeed)
      ((== #t x) succeed))))
         
(define onceo
  (lambda (g)
    (condu
      (g))))

(define prt
  (lambda args
    (lambdag@ (c)
      (begin           
        (for-each
          (lambda (msg)
            (printf "~s~n" msg))
          args)
        (pretty-print c)
        c))))
