;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_135: natural-number decimal digits A, B, and C satisfying
;; the stated power, divisibility, distinctness, and parity conditions form
;; 100*A + 10*B + C = 129. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-135-decimal (a b c)
  (+ (* 100000000 a)
     (+ (* 10000000 b)
        (+ (* 1000000 c)
           (+ (* 100000 a)
              (+ (* 10000 c)
                 (+ (* 1000 c)
                    (+ (* 100 b)
                       (+ (* 10 a)
                          b)))))))))

(defun mathd-numbertheory-135-statement (n a b c)
  (implies
   (and (natp n)
        (natp a)
        (natp b)
        (natp c)
        (equal n (+ (expt 3 17) (expt 3 10)))
        (equal (mod (+ n 1) 11) 0)
        (not (equal a b))
        (not (equal b c))
        (not (equal a c))
        (<= a 9)
        (<= b 9)
        (<= c 9)
        (equal (mod a 2) 1)
        (equal (mod c 2) 1)
        (not (equal (mod b 3) 0))
        (equal n (mathd-numbertheory-135-decimal a b c)))
   (equal (+ (* 100 a)
             (+ (* 10 b) c))
          129)))

(value-triple :itpeval-statement-checked)
:q
