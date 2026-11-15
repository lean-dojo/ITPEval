;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__042, "Sum of the Reciprocals of the Triangular
;; Numbers": for T_k = k(k+1)/2, the exact reciprocal partial sum is
;; sum_{k=1}^n 1/T_k = 2 - 2/(n+1), and these sums converge to 2.
;; This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-042-triangular-number (n)
  (if (natp n)
      (/ (* n (+ n 1)) 2)
    0))

(defun hundred-theorems-042-reciprocal-triangular-prefix (terms)
  (if (zp terms)
      0
    (+ (hundred-theorems-042-reciprocal-triangular-prefix (- terms 1))
       (/ 1
          (hundred-theorems-042-triangular-number terms)))))

(defun hundred-theorems-042-finite-sum-statement (terms)
  (implies
   (natp terms)
   (equal
    (hundred-theorems-042-reciprocal-triangular-prefix terms)
    (- 2 (/ 2 (+ terms 1))))))

;; For positive reduced rational epsilon = p/q, 2q+1 is an internal natural
;; cutoff witness: at every later natural term count the exact error
;; 2/(terms+1) is strictly below epsilon.
(defun hundred-theorems-042-cutoff (epsilon)
  (if (and (rationalp epsilon)
           (< 0 epsilon))
      (+ 1 (* 2 (denominator epsilon)))
    0))

;; Universal predicate matrix for the explicit witness above. Positive
;; rational tolerances are cofinal in the positive reals, so this is
;; equivalent to convergence of the rational-valued prefixes to 2 over R.
(defun hundred-theorems-042-sum-of-reciprocals-statement
    (epsilon terms)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon)
        (natp terms)
        (<= (hundred-theorems-042-cutoff epsilon)
            terms))
   (< (abs
       (- (hundred-theorems-042-reciprocal-triangular-prefix terms)
          2))
      epsilon)))

(value-triple :itpeval-statement-checked)
:q
