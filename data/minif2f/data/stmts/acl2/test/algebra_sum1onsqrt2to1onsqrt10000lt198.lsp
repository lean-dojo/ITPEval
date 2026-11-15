;; Statement-only formalization of miniF2F artifact
;; algebra_sum1onsqrt2to1onsqrt10000lt198: the finite real sum of
;; 1/sqrt(k) for k from 2 through 10000 is less than 198. ACL2 represents
;; each reciprocal as sqrt(k)/k and compares the resulting exact element of
;; a nested quadratic tower. This file contains no proof.

(in-package "ACL2")

;; At a tower level with radicand d, a pair (u . v) denotes
;; u + v*sqrt(d). Rational atoms are embedded unchanged at every level.
(defun algebra-sum1onsqrt2to1onsqrt10000lt198-tower-neg (x radicands)
  (if (and (consp radicands)
           (consp x))
      (cons
       (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-neg
        (car x) (cdr radicands))
       (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-neg
        (cdr x) (cdr radicands)))
    (- x)))

(defun algebra-sum1onsqrt2to1onsqrt10000lt198-tower-add
    (x y radicands)
  (if (and (consp radicands)
           (or (consp x)
               (consp y)))
      (let ((xu (if (consp x) (car x) x))
            (xv (if (consp x) (cdr x) 0))
            (yu (if (consp y) (car y) y))
            (yv (if (consp y) (cdr y) 0))
            (lower-radicands (cdr radicands)))
        (cons
         (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-add
          xu yu lower-radicands)
         (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-add
          xv yv lower-radicands)))
    (+ x y)))

(defun algebra-sum1onsqrt2to1onsqrt10000lt198-tower-sub
    (x y radicands)
  (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-add
   x
   (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-neg
    y radicands)
   radicands))

(defun algebra-sum1onsqrt2to1onsqrt10000lt198-tower-scale
    (q x radicands)
  (if (and (consp radicands)
           (consp x))
      (cons
       (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-scale
        q (car x) (cdr radicands))
       (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-scale
        q (cdr x) (cdr radicands)))
    (* q x)))

(defun algebra-sum1onsqrt2to1onsqrt10000lt198-tower-mul
    (x y radicands)
  (if (and (consp radicands)
           (or (consp x)
               (consp y)))
      (let* ((d (car radicands))
             (lower-radicands (cdr radicands))
             (xu (if (consp x) (car x) x))
             (xv (if (consp x) (cdr x) 0))
             (yu (if (consp y) (car y) y))
             (yv (if (consp y) (cdr y) 0)))
        (cons
         (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-add
          (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-mul
           xu yu lower-radicands)
          (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-scale
           d
           (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-mul
            xv yv lower-radicands)
           lower-radicands)
          lower-radicands)
         (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-add
          (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-mul
           xu yv lower-radicands)
          (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-mul
           xv yu lower-radicands)
          lower-radicands)))
    (* x y)))

;; This exact order test recursively compares u^2 with d*v^2 when the
;; summands u and v*sqrt(d) have opposite signs.
(defun algebra-sum1onsqrt2to1onsqrt10000lt198-tower-nonnegativep
    (x radicands)
  (declare (xargs :measure (acl2-count radicands)))
  (if (consp x)
      (if (consp radicands)
          (let* ((d (car radicands))
                 (lower-radicands (cdr radicands))
                 (u (car x))
                 (v (cdr x))
                 (u-nonnegative
                  (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-nonnegativep
                   u lower-radicands))
                 (v-nonnegative
                  (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-nonnegativep
                   v lower-radicands))
                 (u-squared
                  (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-mul
                   u u lower-radicands))
                 (v-squared-times-d
                  (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-scale
                   d
                   (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-mul
                    v v lower-radicands)
                   lower-radicands)))
            (and
             (rationalp d)
             (< 0 d)
             (if v-nonnegative
                 (or
                  u-nonnegative
                  (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-nonnegativep
                   (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-sub
                    v-squared-times-d
                    u-squared
                    lower-radicands)
                   lower-radicands))
               (and
                u-nonnegative
                (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-nonnegativep
                 (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-sub
                  u-squared
                  v-squared-times-d
                  lower-radicands)
                 lower-radicands)))))
        nil)
    (and (rationalp x)
         (<= 0 x))))

(defun algebra-sum1onsqrt2to1onsqrt10000lt198-tower-positivep
    (x radicands)
  (and
   (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-nonnegativep
    x radicands)
   (not
    (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-nonnegativep
     (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-neg
      x radicands)
     radicands))))

(defun algebra-sum1onsqrt2to1onsqrt10000lt198-radicands-down (n)
  (declare (xargs :measure (nfix n)))
  (if (and (integerp n)
           (< 1 n))
      (cons
       n
       (algebra-sum1onsqrt2to1onsqrt10000lt198-radicands-down
        (- n 1)))
    nil))

;; In the tower headed by d, (rest . 1/d) denotes
;; rest + sqrt(d)/d = rest + 1/sqrt(d).
(defun algebra-sum1onsqrt2to1onsqrt10000lt198-sum (radicands)
  (if (consp radicands)
      (cons
       (algebra-sum1onsqrt2to1onsqrt10000lt198-sum
        (cdr radicands))
       (/ 1 (car radicands)))
    0))

(defun algebra-sum1onsqrt2to1onsqrt10000lt198-statement ()
  (let* ((radicands
          (algebra-sum1onsqrt2to1onsqrt10000lt198-radicands-down
           10000))
         (sum-value
          (algebra-sum1onsqrt2to1onsqrt10000lt198-sum
           radicands))
         (gap
          (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-sub
           198 sum-value radicands)))
    (algebra-sum1onsqrt2to1onsqrt10000lt198-tower-positivep
     gap radicands)))

(value-triple :itpeval-statement-checked)
:q
