;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_3:
;; the sum of the squares from 1 through 9 has remainder 5 modulo 10. This
;; file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-3-statement ()
  (equal
   (mod
    (+ (expt 1 2)
       (+ (expt 2 2)
          (+ (expt 3 2)
             (+ (expt 4 2)
                (+ (expt 5 2)
                   (+ (expt 6 2)
                      (+ (expt 7 2)
                         (+ (expt 8 2)
                            (expt 9 2)))))))))
    10)
   5))

(value-triple :itpeval-statement-checked)
:q
