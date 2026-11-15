;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1968_a2: simultaneous nonzero rational approximation of two
;; integer linear forms with nonzero determinant. This file contains no proof.

(in-package "ACL2")

;; Positive rational tolerances are cofinal in the positive reals. Therefore
;; universal closure over the tolerances below is equivalent to the source's
;; universal closure over positive real epsilon.
;;
;; DEFUN-SK keeps the two unrestricted rational witnesses internal to the
;; statement instead of replacing them by a proof-derived finite search.

(defun putnam-1968-a2-witness-p
    (r s a b c d e f epsilon)
  (let ((first-error
         (abs (- (+ (* r a) (* s b)) e)))
        (second-error
         (abs (- (+ (* r c) (* s d)) f))))
    (and (rationalp r)
         (rationalp s)
         (< 0 first-error)
         (< first-error epsilon)
         (< 0 second-error)
         (< second-error epsilon))))

(defun-sk putnam-1968-a2-witness-exists-p
    (a b c d e f epsilon)
  (exists (r s)
    (putnam-1968-a2-witness-p
     r s a b c d e f epsilon)))

(defun putnambench-putnam-1968-a2-statement
    (a b c d e f epsilon)
  (implies
   (and (integerp a)
        (integerp b)
        (integerp c)
        (integerp d)
        (integerp e)
        (integerp f)
        (not (equal (* a d) (* b c)))
        (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1968-a2-witness-exists-p
    a b c d e f epsilon)))

(value-triple :itpeval-statement-checked)
:q
