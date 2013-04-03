
(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(load "mk.scm")

(printf "==-tests\n")
(load "==-tests.ss")

(printf "symbolo-tests\n")
(load "symbolo-tests.ss")

(printf "numbero-tests\n")
(load "numbero-tests.ss")

(printf "symbolo-numbero-tests\n")
(load "symbolo-numbero-tests.ss")

(printf "disequality-tests\n")
(load "disequality-tests.ss")

(printf "absento-closure-tests\n")
(load "absento-closure-tests.ss")

(printf "absento-tests\n")
(load "absento-tests.ss")

(printf "test-infer\n")
(load "test-infer.ss")

(printf "test-interp\n")
(load "test-interp.ss")

(printf "test-numbers\n")
(load "test-numbers.ss")

(printf "test-quines\n")
(load "test-quines.ss")


