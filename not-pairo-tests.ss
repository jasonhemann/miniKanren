(load "mk.scm")

(test-check "not-pairo 0"
  (run 1 (q) (not-pairo q) (symbolo q))
  '((_.0 (sym _.0))))

(test-check "not-pairo 1"
  (run 1 (q) (symbolo q) (not-pairo q))
  '((_.0 (sym _.0))))

(test-check "not-pairo 2"
  (run 1 (q) (not-pairo q))
  '((_.0 (not-pair _.0))))

(test-check "not-pairo 3"
  (run 1 (q) 
       (fresh (x y)
	 (== x `(1 2))
	 (not-pairo y)
	 (=/= x y)))
  '(_.0))

(test-check "not-pairo 4"
  (run 1 (q) 
       (fresh (x y)
	 (== x `(1 2))
	 (=/= x y)
	 (not-pairo y)))
  '(_.0))

(test-check "not-pairo 5"
  (run 1 (q) 
       (fresh (x y)
	 (=/= x y)
	 (not-pairo y)
	 (== x `(1 2))))
  '(_.0))

(test-check "not-pairo 6"
  (run 1 (q) 
       (fresh (x y)
	 (absento x y)
	 (not-pairo y)
	 (== x `(1 2))))
  '(_.0))

(test-check "not-pairo 7"
  (run 1 (q) 
       (fresh (x y)
	 (absento x y)
	 (== x `(1 2))
	 (not-pairo y)))
  '(_.0))

(test-check "not-pairo 8"
  (run 1 (q) 
       (fresh (x y)
	 (== x `(1 2))
	 (absento x y)
	 (not-pairo y)))
  '(_.0))

(test-check "not-pairo 9"
  (run 1 (q) 
       (fresh (x y)
	 (== x `(1 2))
	 (not-pairo y)
	 (absento x y)))
  '(_.0))

(test-check "not-pairo 10"
  (run 1 (q) 
       (fresh (x y)
	 (== x `(1 2))
	 (not-pairo y)
	 (absento y x)
	 (== `(,x ,y) q)))
  '((((1 2) _.0)
     (=/= ((_.0 ())) ((_.0 1)) ((_.0 2)))
     (not-pair _.0))))

(test-check "not-pairo 11"
  (run 1 (q) (fresh (x) (symbolo q) (== x q)) (not-pairo q))
  '((_.0 (sym _.0))))

(test-check "not-pairo 12"
  (run 1 (q) (fresh (x) (not-pairo q) (== x q)) (symbolo q))
  '((_.0 (sym _.0))))

(test-check "not-pairo 13"
  (run 1 (q) (not-pairo #f))
  '(_.0))

(test-check "not-pairo 14"
  (run 1 (q) (not-pairo 5))
  '(_.0))

(test-check "not-pairo 15"
  (run 1 (q) (== q #f) (not-pairo q))
  '(#f))

(test-check "not-pairo 16"
  (run 1 (q) (== q '()) (not-pairo q))
  '(()))

(test-check "not-pairo 17"
  (run 1 (a) (fresh (b c) (== b a) (== c a) (not-pairo c) (symbolo b)))
  '((_.0 (sym _.0))))


