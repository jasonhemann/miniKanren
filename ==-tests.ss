(load "mk.scm")

(test-check "1"
    (run 1 (q) (== 5 q))
  '(5))

(test-check "2"
  (run* (q)
  (conde
    [(== 5 q)]
    [(== 6 q)]))
  '(5 6))

(test-check "3"
  (run* (q)
  (fresh (a d)
    (conde
      [(== 5 a)]
      [(== 6 d)])
    (== `(,a . ,d) q)))
  '((5 . _.0) (_.0 . 6)))

(define appendo
  (lambda (l s out)
    (conde
      [(== '() l) (== s out)]
      [(fresh (a d res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out)
         (appendo d s res))])))

(test-check "4"
  (run* (q) (appendo '(a b c) '(d e) q))
  '((a b c d e)))

(test-check "5"
  (run* (q) (appendo q '(d e) '(a b c d e)))
  '((a b c)))

(test-check "6"
  (run* (q) (appendo '(a b c) q '(a b c d e)))
  '((d e)))

(test-check "7"
  (run 5 (q)
  (fresh (l s out)    
    (appendo l s out)
    (== `(,l ,s ,out) q)))
  '((() _.0 _.0)
  ((_.0) _.1 (_.0 . _.1))
  ((_.0 _.1) _.2 (_.0 _.1 . _.2))
  ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
  ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))))
