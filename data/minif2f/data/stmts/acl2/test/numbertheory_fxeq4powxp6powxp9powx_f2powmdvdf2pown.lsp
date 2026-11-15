;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown: for positive natural
;; numbers m <= n and f(x) = 4^x + 6^x + 9^x, f(2^m) divides f(2^n).
;; This file contains no proof.

(in-package "ACL2")

(defun numbertheory-fxeq4powxp6powxp9powx-f2powmdvdf2pown-f (x)
  (+ (+ (expt 4 x)
        (expt 6 x))
     (expt 9 x)))

(defun numbertheory-fxeq4powxp6powxp9powx-f2powmdvdf2pown-statement (m n)
  (implies
   (and (natp m)
        (natp n)
        (< 0 m)
        (< 0 n)
        (<= m n))
   (equal
    (mod
     (numbertheory-fxeq4powxp6powxp9powx-f2powmdvdf2pown-f (expt 2 n))
     (numbertheory-fxeq4powxp6powxp9powx-f2powmdvdf2pown-f (expt 2 m)))
    0)))

(value-triple :itpeval-statement-checked)
:q
