
(test-check "test 0"
  (run 1 (q) (absento q q))
  '())

(test-check "test 1"
  (run 1 (q)
    (fresh (a b c)
      (== a b)
      (absento b c)
      (== c b)
      (== `(,a ,b ,c) q)))
  '())

(test-check "test 2"
  (run 1 (q)
     (fresh (a)
       (absento q a)
       (absento `((,q ,q) 3 (,q ,q)) `(,a 3 ,a))))
  '(_.0))

(test-check "test 3"
  (run 1 (q)
     (fresh (a b)
       (absento q a)
       (absento `(3 ,a) `(,b ,a))
       (== 3 b)))
  '())

(test-check "test 4"
  (run 1 (q)
     (fresh (a b)
       (absento q a)
       (absento `(3 ,a) `(,q ,a))
       (== 3 b)))
  '((_.0 (=/= ((_.0 3))))))

(test-check "test 5"
  (run 1 (q)
     (fresh (a b)
       (numbero a)
       (numbero b)
       (absento '(3 3) `(,a ,b))
       (=/= a b)
       (== `(,a ,b) q)))
  '(((_.0 _.1) (=/= ((_.0 _.1))) (num _.0 _.1))))

(test-check "test 6"
  (run 1 (q) (fresh (a) (absento q a) (== q a)))
  '())

(test-check "test 7"
   (run 1 (q)
    (fresh (a b c)
      (absento '(3 . 4) c)
      (== `(,a . ,b) c)
      (== q `(,a . ,b))))
  '(((_.0 . _.1) (=/= ((_.0 3) (_.1 4))) (absento ((3 . 4) _.0) ((3 . 4) _.1)))))

(test-check "test 8"
  (run 1 (q)
    (fresh (a b)
      (absento 5 a)
      (symbolo b)
      (== `(,q ,b) a)))
  '((_.0 (absento (5 _.0)))))

(test-check "test 9"
  (run 1 (q)
    (fresh (a b)
      (absento 5 a)
      (== `(,q ,b) a)))
  '((_.0 (absento (5 _.0)))))

(test-check "test 10"
  (run 1 (q) (fresh (a) (absento `(3 . ,a) q) (absento q `(3 . ,a))))
   '((_.0 (=/= ((_.0 3))))))

(test-check "test 11"
  (run 1 (q)
    (fresh (a b c d e f)
      (absento `(,a . ,b) q)
      (absento q `(,a . ,b))
      (== `(,c . ,d) a)
      (== `(3 . ,e) c)
      (== `(,f . 4) d)))
  '((_.0 (=/= ((_.0 3)) ((_.0 4))))))

(test-check "test 12"
  (run 1 (q)
    (fresh (a b c)
      (absento `(,3 . ,a) `(,b . ,c))
      (numbero b)
      (== `(,a ,b ,c) q)))
    '(((_.0 _.1 _.2) (=/= ((_.0 _.2) (_.1 3))) (num _.1) (absento ((3 . _.0) _.2)))))

(test-check "test 13"
  (run 1 (q)
    (fresh (a b c)
      (== `(,a . ,b) q)
      (absento '(3 . 4) q)
      (numbero a)
      (numbero b)))
  '(((_.0 . _.1) (=/= ((_.0 3) (_.1 4))) (num _.0 _.1))))

(test-check "test 14"
   (run 1 (q)
    (fresh (a b)
      (absento '(3 . 4) `(,a . ,b))
      (== `(,a . ,b) q)))
  '(((_.0 . _.1) (=/= ((_.0 3) (_.1 4))) (absento ((3 . 4) _.0) ((3 . 4) _.1)))))

(test-check "test 15"
  (run 1 (q)
    (absento q `(3 . (4 . 5))))
  '((_.0 (=/= ((_.0 3))
              ((_.0 4))
              ((_.0 5))
              ((_.0 (3 . (4 . 5))))
              ((_.0 (4 . 5)))))))

(test-check "test 16"
  (run 1 (q)
    (fresh (a b x)
      (absento a b)
      (symbolo a)
      (numbero x)
      (== x b)
      (== `(,a ,b) q)))
  '(((_.0 _.1) (num _.1) (sym _.0))))

(test-check "test 19"
  (run* (q) (absento 5 q) (absento 5 q))
  '((_.0 (absento (5 _.0)))))

(test-check "test 20"
  (run* (q) (absento 5 q) (absento 6 q))
  '((_.0 (absento (5 _.0) (6 _.0)))))

(test-check "test 21"
  (run* (q) (absento 5 q) (symbolo q))
  '((_.0 (sym _.0))))

(test-check "test 22"
  (run* (q) (numbero q) (absento 'tag q))
  '((_.0 (num _.0))))

(test-check "test 23"
  (run* (q) (absento 'tag q) (numbero q))
  '((_.0 (num _.0))))

(test-check "test 24"
  (run* (q) (== 5 q) (absento 5 q))
  '())

(test-check "test 25"
  (run* (q) (== q `(5 6)) (absento 5 q))
  '())

(test-check "test 25b"
  (run* (q) (absento 5 q) (== q `(5 6)))
  '())

(test-check "test 26"
  (run* (q) (absento 5 q) (== 5 q))
  '())

(test-check "test 27"
  (run* (q) (absento 'tag1 q) (absento 'tag2 q))
  '((_.0 (absento (tag1 _.0) (tag2 _.0)))))

(test-check "test 28"
  (run* (q) (absento 'tag q) (numbero q))
  '((_.0 (num _.0))))

(test-check "test 29"
   (run* (q)
    (fresh (a b)
      (absento a b)
      (absento b a)
      (== `(,a ,b) q)
      (symbolo a)
      (numbero b)))
  '(((_.0 _.1) (num _.1) (sym _.0))))

(test-check "test 30"
  (run* (q)
    (fresh (a b)
      (absento b a)
      (absento a b)
      (== `(,a ,b) q)
      (symbolo a)
      (symbolo b)))
  '(((_.0 _.1) (=/= ((_.0 _.1))) (sym _.0 _.1))))

(test-check "test 31"
  (run* (q)
    (fresh (a b)
      (absento a b)
      (absento b a)
      (== `(,a ,b) q)))
  '(((_.0 _.1) (absento (_.0 _.1) (_.1 _.0)))))

(test-check "test 32"
  (run 1 (q)
    (fresh (a b)
      (absento 5 a)
      (absento 5 b)
      (== `(,a . ,b) q)))
  '(((_.0 . _.1) (absento (5 _.0) (5 _.1)))))

(test-check "test 33"
  (run 1 (q)
    (fresh (a b c)
      (== `(,a ,b) c)
      (== `(,c ,c) q)
      (symbolo b)
      (numbero c)))
  '())

(test-check "test 34"
  (run 1 (q) (absento 'tag q) (symbolo q))
  '((_.0 (=/= ((_.0 tag))) (sym _.0))))

(test-check "test 35"
  (run 1 (q) (absento 5 q) (numbero q))
  '((_.0 (=/= ((_.0 5))) (num _.0))))

(test-check "test 36"
  (run 1 (q)
    (fresh (a)
      (== 5 a) (absento a q)))
  '((_.0 (absento (5 _.0)))))

(test-check "test 37"
  (run* (q)
    (fresh (a b)
      (absento a b)
      (absento b a)
      (== `(,a ,b) q)
      (symbolo a)
      (symbolo b)))
  '(((_.0 _.1) (=/= ((_.0 _.1))) (sym _.0 _.1))))

(test-check "test 38"
  (run 1 (q) (absento '() q))
  '((_.0 (absento (() _.0)))))

(test-check "test 39"
  (run 1 (q) (absento `(3 4) q))
  '((_.0 (absento ((3 4) _.0)))))

(test-check "test 40"
  (run 1 (q)
    (fresh (d a c)
      (== `(3 . ,d) q)
      (=/= `(,c . ,a) q)
      (== '(3 . 4) d)))
  '((3 3 . 4)))

(test-check "test 41"
  (run 1 (q)
    (fresh (a)
      (== `(,a . ,a) q)))
  '((_.0 . _.0)))

(test-check "test 42"
  (run 1 (q)
    (fresh (a b)
      (==  `((3 4) (5 6)) q)
      (absento `(3 4) q)))
  '())

(test-check "test 43"
  (run 1 (q) (absento q 3))
  '((_.0 (=/= ((_.0 3))))))

(test-check "test 44"
  (run* (q)
    (fresh (a b)
      (absento a b)
      (absento b a)
      (== `(,a ,b) q)))
  '(((_.0 _.1) (absento (_.0 _.1) (_.1 _.0)))))

(test-check "test 45"
  (run 1 (q)
    (fresh (a b)
      (absento `(,a . ,b) q)
      (== q `(3 . (,b . ,b)))))
  '((3 _.0 . _.0)))

(test-check "test 45b"
  (run 1 (q)
    (fresh (a b)
      (absento `(,a . ,b) q)
      (== q `(,a 3 . (,b . ,b)))))
  '(((_.0 3 _.1 . _.1) (=/= ((_.0 _.1))))))

(test-check "test 46"
  (run 1 (q)
    (fresh (a)
      (absento a q)
      (absento q a)))
  '(_.0))

(test-check "test 47"
  (run 1 (q)
    (fresh (a)
      (absento `(,a . 3) q)))
  '(_.0)) 

(test-check "test 48"
  (run 1 (q)
    (fresh (a)
      (absento `(,a . 3) q)))
  '(_.0))

(test-check "test 49"
  (run 1 (q)
    (fresh (a b c d e)
      (absento `((3 4 ,a) (4 ,b) ((,c)) ,d ,e) q)))
  '(_.0))

(test-check "test 50"
  (run 1 (q) (fresh (a)
	       (absento a q)
	       (== 5 a)))
  '((_.0 (absento (5 _.0)))))

(test-check "test 51"
  (run 1 (q) (fresh (a b c d)
	       (== a 5)
	       (== a b)
	       (== b c)
	       (absento d q)
	       (== c d)))
  '((_.0 (absento (5 _.0)))))

(test-check "test 52"
  (run 1 (q) (fresh (a b c d)
	       (== a b)
	       (== b c)
	       (absento a q)
	       (== c d)
	       (== d 5)))
  '((_.0 (absento (5 _.0)))))

(test-check "test 53"
  (run 1 (q)
    (fresh (t1 t2 a)
      (== `(,a . 3) t1)
      (== `(,a . (4 . 3)) t2)
      (== `(,t1 ,t2) q)
      (absento t1 t2)))
  '((((_.0 . 3) (_.0 4 . 3)) (=/= ((_.0 4))))))

(test-check "test 54"
  (run 1 (q)
    (fresh (a)
      (== `(,a . 3) q)
      (absento q `(,a . (4 . 3)))))
  '(((_.0 . 3) (=/= ((_.0 4))))))

(test-check "test 55"
  (run 1 (q) (fresh (a d c)
	       (== '(3 . 4) d)
	       (absento `(3 . 4) q)
	       (== `(3 . ,d) q)))
  '())

(test-check "test 56"
  (run* (q) (fresh (a b)
	      (absento a b)
	      (absento b a)
	      (== `(,a ,b) q)
	      (symbolo a)
	      (numbero b)))
  '(((_.0 _.1) (num _.1) (sym _.0))))


(test-check "test 57"
  (run 1 (q)
    (numbero q)
    (absento q 3))
  '((_.0 (=/= ((_.0 3))) (num _.0))))

(test-check "test 58"
  (run 1 (q)
    (fresh (a)
      (== `(,a . 3) q)
      (absento q `(,a . (4 . (,a . 3))))))
  '())

(test-check "test 59"
  (run 1 (q) 
    (fresh (a) 
      (== `(,a . 3) q)
      (absento q `(,a . ((,a . 3) . (,a . 4))))))
  '())

(test-check "test 60"
  (run 1 (q)
    (fresh (a d c)
      (== `(3 . ,d) q)
      (== '(3 . 4) d)
      (absento `(3 . 4) q)))
  '())

(test-check "test 61"
  (run 1 (q)
    (fresh (a b c)
      (symbolo b)
      (absento `(,3 . ,a) `(,b . ,c))
      (== `(,a ,b ,c) q)))
  '(((_.0 _.1 _.2) (sym _.1) (absento ((3 . _.0) _.2)))))

(test-check "test 62"
  (run 1 (q) (fresh (a b c) (absento a b) (absento b c) (absento c q) (symbolo a)))
  '(_.0))

(test-check "test 63"
  (run 1 (q) (fresh (a b c) (=/= a b) (=/= b c) (=/= c q) (symbolo a)))
  '(_.0))

(test-check "test 64"
  (run 1 (q) (symbolo q) (== 'tag q))
  '(tag))

(test-check "test 65"
  (run 1 (q) (fresh (b) (absento '(3 4) `(,q ,b))))
  '((_.0 (absento ((3 4) _.0)))))

(test-check "test 66"
  (run 1 (q) (absento 6 5))
  '(_.0))

(test-check "test 67"
  (run 1 (q)
    (fresh (a b)
      (=/= a b)
      (symbolo a)
      (numbero b)
      (== `(,a ,b) q)))
  '(((_.0 _.1) (num _.1) (sym _.0))))

(test-check "test 68"
  (run 1 (q)
    (fresh (a b c d)
      (=/= `(,a ,b) `(,c ,d))
      (symbolo a)
      (numbero c)
      (symbolo b)
      (numbero c)
      (== `(,a ,b ,c ,d) q)))
  '(((_.0 _.1 _.2 _.3) (num _.2) (sym _.0 _.1))))

(test-check "test 69"
  (run 1 (q) (fresh (a b) (=/= `(,a . 3) `(,b . 3)) (symbolo a) (numbero b) (== `(,a ,b) q)))
   '(((_.0 _.1) (num _.1) (sym _.0))))

(test-check "test 70"
  (run* (q) (fresh (a b)
	      (absento a b)
	      (absento b a)
	      (== `(,a ,b) q)
	      (symbolo a)
	      (numbero b)))
  '(((_.0 _.1) (num _.1) (sym _.0))))

(test-check "test 70b"
  (run* (q) (fresh (a b)
              (symbolo a)
              (numbero b)
              (absento a b)
              (absento b a)
              (== `(,a ,b) q)))
  '(((_.0 _.1) (num _.1) (sym _.0))))

(test-check "test 71"
  (run* (q) (fresh (a b)
	      (absento a b)
	      (absento b a)
	      (== `(,a ,b) q)
	      (symbolo a)
	      (symbolo b)))
  '(((_.0 _.1) (=/= ((_.0 _.1))) (sym _.0 _.1))))

(test-check "test 72"
  (run* (q)
    (fresh (a b)
      (absento a b)
      (absento b a)
      (== `(,a ,b) q)))
  '(((_.0 _.1) (absento (_.0 _.1) (_.1 _.0)))))

(test-check "test 73"
  (run 1 (q)
    (fresh (a b)
      (== `(,a ,b) q)
      (absento b a)
      (absento a b)
      (== a '(1 . 2))))
  '((((1 . 2) _.0)
   (=/= ((_.0 1)) ((_.0 2)))
   (absento ((1 . 2) _.0)))))

(test-check "test 74"
  (run 1 (q)
    (fresh (a b c)
      (absento a q)
      (absento q a)
      (== `(,b . ,c) a)
      (== '(1 . 2) b)
      (== '(3 . 4) c)))
  '((_.0 (=/= ((_.0 1)) ((_.0 2)) ((_.0 3)) ((_.0 4))
           ((_.0 (1 . 2))) ((_.0 (3 . 4))))
      (absento (((1 . 2) 3 . 4) _.0)))))

(test-check "test 75"
   (run 1 (q)
     (fresh (a b c d e f g)
       (absento a q)
       (absento q a)
       (== `(,b . ,c) a)
       (== `(,d . ,e) b)
       (== `(,f . ,g) c)
       (== '(1 . 2) d)
       (== '(3 . 4) e)
       (== '(5 . 6) f)
       (== '(7 . 8) g)))
   '((_.0 (=/= ((_.0 1))
               ((_.0 2))
               ((_.0 3))
               ((_.0 4))
               ((_.0 5))
               ((_.0 6))
               ((_.0 7))
               ((_.0 8))
               ((_.0 (1 . 2)))
               ((_.0 (3 . 4)))
               ((_.0 (5 . 6)))
               ((_.0 (7 . 8)))
               ((_.0 ((1 . 2) 3 . 4)))
               ((_.0 ((5 . 6) 7 . 8))))
          (absento ((((1 . 2) 3 . 4) (5 . 6) 7 . 8) _.0)))))

(test-check "test 76"
   (run 1 (q)
     (absento 3 q)
     (absento '(3 4) q))
   '((_.0 (absento (3 _.0)))))

(test-check "test 77"
  (run 1 (q)
     (fresh (x a b)
       (== x `(,a ,b))
       (absento '(3 4) x)
       (absento 3 a)
       (absento 4 b)
       (== q `(,a 2))))
  '(((_.0 2) (absento (3 _.0)))))

(test-check "test 78"
  (run 1 (q)
    (fresh (d)
      (== `(3 . ,d) q)
      (absento `(3 . 4) q)
      (== '(3 . 4) d)))
  '())

(test-check "test 79"
  (run 1 (q)
    (fresh (d)
      (absento `(3 . 4) q)
      (== `(3 . ,d) q)
      (== '(3 . 4) d)))
  '())

(test-check "test 80"
  (run 1 (q)
    (fresh (d a c)
      (== `(3 . ,d) q)
      (absento `(3 . ,a) q)
      (== c d)
      (== `(3 . ,a) c)))
  '())

(test-check "test 81"
  (run 1 (q)
    (fresh (a b)
      (absento `(3 . ,a) `(,b . 4))
      (== `(,a . ,b) q)))
  '(((_.0 . _.1) (=/= ((_.0 4) (_.1 3))) (absento ((3 . _.0) _.1)))))

(test-check "test 82"
  (run 1 (q)
    (fresh (d)
      (== `(3 . ,d) q)
      (absento `(3 . 4) q)))
  '(((3 . _.0) (=/= ((_.0 4))) (absento ((3 . 4) _.0)))))

(test-check "test 83"
  (run 1 (q)
    (fresh (d)
      (== `(3 . ,d) q)
      (== '(3 . 4) d))
      (absento `(3 . 4) q))
  '())

(test-check "test 84"
  (run 1 (q) 
    (fresh (a b c d) 
      (=/= `(,a . ,b) `(,c . ,d)) 
      (absento a c) 
      (== `(,a ,b ,c ,d) q)))
  '(((_.0 _.1 _.2 _.3) (absento (_.0 _.2)))))

(test-check "test 84 b"
  (run 1 (q) 
    (fresh (a b c d) 
      (=/= `(,a . ,b) `(,c . ,d)) 
      (absento c a) 
      (== `(,a ,b ,c ,d) q)))
  '(((_.0 _.1 _.2 _.3) (absento (_.2 _.0)))))
