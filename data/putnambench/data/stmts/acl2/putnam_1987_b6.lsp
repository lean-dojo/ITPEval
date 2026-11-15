;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_b6:
;; in a field of odd-prime-square order, an orientation of the nonzero
;; additive-inverse pairs meets its doubled image in an even number of
;; elements. This file contains no proof.

(in-package "ACL2")

;; CARRIER and S are duplicate-free enumerations of the finite field and its
;; distinguished subset. ADD, MUL, NEG, and INV are ACL2 function objects,
;; rather than operation tables. Every finite field and subset in the source
;; has such an enumeration and tame finite-function presentation, while the
;; predicates below recover exactly the induced field structure and set.

(defun putnam-1987-b6-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1987-b6-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1987-b6-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1987-b6-no-divisor-through-p
    p (- p 1))))

(defun putnam-1987-b6-unary (function x)
  (apply$ function (list x)))

(defun putnam-1987-b6-binary (function x y)
  (apply$ function (list x y)))

(defun putnam-1987-b6-subset-p (xs carrier)
  (if (endp xs)
      t
    (and
     (member-equal (car xs) carrier)
     (putnam-1987-b6-subset-p (cdr xs) carrier))))

(defun putnam-1987-b6-unary-closed-p
    (xs carrier function)
  (if (endp xs)
      t
    (and
     (member-equal
      (putnam-1987-b6-unary function (car xs))
      carrier)
     (putnam-1987-b6-unary-closed-p
      (cdr xs) carrier function))))

(defun putnam-1987-b6-binary-row-closed-p
    (x ys carrier function)
  (if (endp ys)
      t
    (and
     (member-equal
      (putnam-1987-b6-binary function x (car ys))
      carrier)
     (putnam-1987-b6-binary-row-closed-p
      x (cdr ys) carrier function))))

(defun putnam-1987-b6-binary-closed-p
    (xs carrier function)
  (if (endp xs)
      t
    (and
     (putnam-1987-b6-binary-row-closed-p
      (car xs) carrier carrier function)
     (putnam-1987-b6-binary-closed-p
      (cdr xs) carrier function))))

(defun putnam-1987-b6-commutative-row-p
    (x ys function)
  (if (endp ys)
      t
    (and
     (equal
      (putnam-1987-b6-binary function x (car ys))
      (putnam-1987-b6-binary function (car ys) x))
     (putnam-1987-b6-commutative-row-p
      x (cdr ys) function))))

(defun putnam-1987-b6-commutative-p
    (xs carrier function)
  (if (endp xs)
      t
    (and
     (putnam-1987-b6-commutative-row-p
      (car xs) carrier function)
     (putnam-1987-b6-commutative-p
      (cdr xs) carrier function))))

(defun putnam-1987-b6-associative-third-p
    (x y zs function)
  (if (endp zs)
      t
    (and
     (equal
      (putnam-1987-b6-binary
       function
       (putnam-1987-b6-binary function x y)
       (car zs))
      (putnam-1987-b6-binary
       function
       x
       (putnam-1987-b6-binary function y (car zs))))
     (putnam-1987-b6-associative-third-p
      x y (cdr zs) function))))

(defun putnam-1987-b6-associative-second-p
    (x ys carrier function)
  (if (endp ys)
      t
    (and
     (putnam-1987-b6-associative-third-p
      x (car ys) carrier function)
     (putnam-1987-b6-associative-second-p
      x (cdr ys) carrier function))))

(defun putnam-1987-b6-associative-p
    (xs carrier function)
  (if (endp xs)
      t
    (and
     (putnam-1987-b6-associative-second-p
      (car xs) carrier carrier function)
     (putnam-1987-b6-associative-p
      (cdr xs) carrier function))))

(defun putnam-1987-b6-distributive-third-p
    (x y zs add mul)
  (if (endp zs)
      t
    (and
     (equal
      (putnam-1987-b6-binary
       mul
       x
       (putnam-1987-b6-binary add y (car zs)))
      (putnam-1987-b6-binary
       add
       (putnam-1987-b6-binary mul x y)
       (putnam-1987-b6-binary mul x (car zs))))
     (putnam-1987-b6-distributive-third-p
      x y (cdr zs) add mul))))

(defun putnam-1987-b6-distributive-second-p
    (x ys carrier add mul)
  (if (endp ys)
      t
    (and
     (putnam-1987-b6-distributive-third-p
      x (car ys) carrier add mul)
     (putnam-1987-b6-distributive-second-p
      x (cdr ys) carrier add mul))))

(defun putnam-1987-b6-distributive-p
    (xs carrier add mul)
  (if (endp xs)
      t
    (and
     (putnam-1987-b6-distributive-second-p
      (car xs) carrier carrier add mul)
     (putnam-1987-b6-distributive-p
      (cdr xs) carrier add mul))))

(defun putnam-1987-b6-identity-inverse-laws-p
    (xs zero one add mul neg inv)
  (if (endp xs)
      t
    (let* ((x (car xs))
           (negative-x
            (putnam-1987-b6-unary neg x))
           (inverse-x
            (putnam-1987-b6-unary inv x)))
      (and
       (equal
        (putnam-1987-b6-binary add x zero)
        x)
       (equal
        (putnam-1987-b6-binary add x negative-x)
        zero)
       (equal
        (putnam-1987-b6-binary mul x one)
        x)
       (if (equal x zero)
           (equal inverse-x zero)
         (equal
          (putnam-1987-b6-binary mul x inverse-x)
          one))
       (putnam-1987-b6-identity-inverse-laws-p
        (cdr xs) zero one add mul neg inv)))))

(defun putnam-1987-b6-field-p
    (carrier zero one add mul neg inv)
  (and
   (true-listp carrier)
   (consp carrier)
   (no-duplicatesp-equal carrier)
   (member-equal zero carrier)
   (member-equal one carrier)
   (not (equal zero one))
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (putnam-1987-b6-unary-closed-p
    carrier carrier neg)
   (putnam-1987-b6-unary-closed-p
    carrier carrier inv)
   (putnam-1987-b6-binary-closed-p
    carrier carrier add)
   (putnam-1987-b6-binary-closed-p
    carrier carrier mul)
   (putnam-1987-b6-commutative-p
    carrier carrier add)
   (putnam-1987-b6-commutative-p
    carrier carrier mul)
   (putnam-1987-b6-associative-p
    carrier carrier add)
   (putnam-1987-b6-associative-p
    carrier carrier mul)
   (putnam-1987-b6-distributive-p
    carrier carrier add mul)
   (putnam-1987-b6-identity-inverse-laws-p
    carrier zero one add mul neg inv)))

(defun putnam-1987-b6-all-nonzero-p (xs zero)
  (if (endp xs)
      t
    (and
     (not (equal (car xs) zero))
     (putnam-1987-b6-all-nonzero-p
      (cdr xs) zero))))

(defun putnam-1987-b6-oriented-p
    (xs s zero neg)
  (if (endp xs)
      t
    (let* ((x (car xs))
           (negative-x
            (putnam-1987-b6-unary neg x)))
      (and
       (if (equal x zero)
           t
         (if (member-equal x s)
             (not (member-equal negative-x s))
           (member-equal negative-x s)))
       (putnam-1987-b6-oriented-p
        (cdr xs) s zero neg)))))

(defun putnam-1987-b6-doubled-member-p
    (x s add)
  (if (endp s)
      nil
    (or
     (equal
      x
      (putnam-1987-b6-binary
       add (car s) (car s)))
     (putnam-1987-b6-doubled-member-p
      x (cdr s) add))))

(defun putnam-1987-b6-intersection-count
    (carrier s add)
  (if (endp carrier)
      0
    (+
     (if (and
          (member-equal (car carrier) s)
          (putnam-1987-b6-doubled-member-p
           (car carrier) s add))
         1
       0)
     (putnam-1987-b6-intersection-count
      (cdr carrier) s add))))

(defun putnambench-putnam-1987-b6-statement
    (p carrier zero one add mul neg inv s)
  (implies
   (and
    (putnam-1987-b6-prime-p p)
    (equal (mod p 2) 1)
    (putnam-1987-b6-field-p
     carrier zero one add mul neg inv)
    (equal (len carrier) (* p p))
    (true-listp s)
    (no-duplicatesp-equal s)
    (putnam-1987-b6-subset-p s carrier)
    (putnam-1987-b6-all-nonzero-p s zero)
    (equal (* 2 (len s))
           (- (* p p) 1))
    (putnam-1987-b6-oriented-p
     carrier s zero neg))
   (evenp
    (putnam-1987-b6-intersection-count
     carrier s add))))

(value-triple :itpeval-statement-checked)
:q
