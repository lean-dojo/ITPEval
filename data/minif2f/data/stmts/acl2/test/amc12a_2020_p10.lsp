;; Statement-only formalization of miniF2F artifact amc12a_2020_p10:
;; for a natural n > 1, the stated nested logarithm equality implies that
;; the decimal digit sum of n is 13. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no full real logarithm. The arbitrary carrier, ordered
;; field operations, rational embedding, and generic logarithm laws below are
;; explicit premises. The source logarithms remain in the statement; no
;; solved logarithmic coordinate or precomputed value of n is substituted.

(defstub amc20p10-real-p (real-type value) t)
(defstub amc20p10-zero (real-type) t)
(defstub amc20p10-one (real-type) t)
(defstub amc20p10-add (real-type left right) t)
(defstub amc20p10-mul (real-type left right) t)
(defstub amc20p10-neg (real-type value) t)
(defstub amc20p10-inv (real-type value) t)
(defstub amc20p10-le (real-type left right) t)
(defstub amc20p10-of-rational (real-type rational) t)
(defstub amc20p10-log (real-type value) t)

(defun amc20p10-div (real-type x y)
  (amc20p10-mul real-type x (amc20p10-inv real-type y)))

(defun amc20p10-lt (real-type x y)
  (and
   (amc20p10-le real-type x y)
   (not (equal x y))))

(defun amc20p10-positive-p (real-type x)
  (and
   (amc20p10-real-p real-type x)
   (amc20p10-lt real-type (amc20p10-zero real-type) x)))

(defun amc20p10-logb (real-type base argument)
  (amc20p10-div
   real-type
   (amc20p10-log real-type argument)
   (amc20p10-log real-type base)))

(defun-sk amc20p10-closure-laws-p (real-type)
  (forall (x y)
    (and
     (amc20p10-real-p real-type (amc20p10-zero real-type))
     (amc20p10-real-p real-type (amc20p10-one real-type))
     (implies
      (amc20p10-real-p real-type x)
      (and
       (amc20p10-real-p real-type (amc20p10-neg real-type x))
       (amc20p10-real-p real-type (amc20p10-inv real-type x))))
     (implies
      (and
       (amc20p10-real-p real-type x)
       (amc20p10-real-p real-type y))
      (and
       (amc20p10-real-p real-type (amc20p10-add real-type x y))
       (amc20p10-real-p real-type (amc20p10-mul real-type x y)))))))

(defun-sk amc20p10-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc20p10-real-p real-type x)
      (amc20p10-real-p real-type y)
      (amc20p10-real-p real-type z))
     (let ((zero (amc20p10-zero real-type))
           (one (amc20p10-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (amc20p10-add real-type x y)
         (amc20p10-add real-type y x))
        (equal
         (amc20p10-add real-type (amc20p10-add real-type x y) z)
         (amc20p10-add real-type x (amc20p10-add real-type y z)))
        (equal (amc20p10-add real-type x zero) x)
        (equal
         (amc20p10-add real-type x (amc20p10-neg real-type x))
         zero)
        (equal
         (amc20p10-mul real-type x y)
         (amc20p10-mul real-type y x))
        (equal
         (amc20p10-mul real-type (amc20p10-mul real-type x y) z)
         (amc20p10-mul real-type x (amc20p10-mul real-type y z)))
        (equal (amc20p10-mul real-type x one) x)
        (equal
         (amc20p10-mul
          real-type x (amc20p10-add real-type y z))
         (amc20p10-add
          real-type
          (amc20p10-mul real-type x y)
          (amc20p10-mul real-type x z)))
        (equal (amc20p10-inv real-type zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (amc20p10-mul real-type x (amc20p10-inv real-type x))
          one)))))))

(defun-sk amc20p10-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc20p10-real-p real-type x)
      (amc20p10-real-p real-type y)
      (amc20p10-real-p real-type z))
     (let ((zero (amc20p10-zero real-type)))
       (and
        (amc20p10-le real-type x x)
        (implies
         (and
          (amc20p10-le real-type x y)
          (amc20p10-le real-type y x))
         (equal x y))
        (implies
         (and
          (amc20p10-le real-type x y)
          (amc20p10-le real-type y z))
         (amc20p10-le real-type x z))
        (or
         (amc20p10-le real-type x y)
         (amc20p10-le real-type y x))
        (implies
         (amc20p10-le real-type x y)
         (amc20p10-le
          real-type
          (amc20p10-add real-type x z)
          (amc20p10-add real-type y z)))
        (implies
         (and
          (amc20p10-le real-type zero x)
          (amc20p10-le real-type zero y))
         (amc20p10-le
          real-type zero (amc20p10-mul real-type x y))))))))

(defun-sk amc20p10-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (amc20p10-real-p
       real-type (amc20p10-of-rational real-type p))
      (equal
       (amc20p10-of-rational real-type 0)
       (amc20p10-zero real-type))
      (equal
       (amc20p10-of-rational real-type 1)
       (amc20p10-one real-type))
      (equal
       (amc20p10-of-rational real-type (+ p q))
       (amc20p10-add
        real-type
        (amc20p10-of-rational real-type p)
        (amc20p10-of-rational real-type q)))
      (equal
       (amc20p10-of-rational real-type (* p q))
       (amc20p10-mul
        real-type
        (amc20p10-of-rational real-type p)
        (amc20p10-of-rational real-type q)))
      (iff
       (equal p q)
       (equal
        (amc20p10-of-rational real-type p)
        (amc20p10-of-rational real-type q)))
      (iff
       (<= p q)
       (amc20p10-le
        real-type
        (amc20p10-of-rational real-type p)
        (amc20p10-of-rational real-type q)))))))

(defun-sk amc20p10-log-laws-p (real-type)
  (forall (x y)
    (implies
     (and
      (amc20p10-positive-p real-type x)
      (amc20p10-positive-p real-type y))
     (and
      (amc20p10-real-p real-type (amc20p10-log real-type x))
      (equal
       (amc20p10-log
        real-type (amc20p10-mul real-type x y))
       (amc20p10-add
        real-type
        (amc20p10-log real-type x)
        (amc20p10-log real-type y)))
      (equal
       (amc20p10-log
        real-type (amc20p10-inv real-type x))
       (amc20p10-neg real-type (amc20p10-log real-type x)))
      (iff
       (equal
        (amc20p10-log real-type x)
        (amc20p10-log real-type y))
       (equal x y))))))

(defun amc20p10-real-log-structure-p (real-type)
  (and
   (amc20p10-closure-laws-p real-type)
   (amc20p10-field-laws-p real-type)
   (amc20p10-order-laws-p real-type)
   (amc20p10-rational-laws-p real-type)
   (amc20p10-log-laws-p real-type)
   (equal
    (amc20p10-log real-type (amc20p10-one real-type))
    (amc20p10-zero real-type))))

(defun amc20p10-digit-sum-aux (fuel n)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (zp n))
      0
    (+ (mod n 10)
       (amc20p10-digit-sum-aux
        (- fuel 1)
        (floor n 10)))))

(defun amc20p10-digit-sum (n)
  (amc20p10-digit-sum-aux (+ 1 (nfix n)) n))

(defun amc12a-2020-p10-statement (real-type n)
  (let ((two (amc20p10-of-rational real-type 2))
        (four (amc20p10-of-rational real-type 4))
        (sixteen (amc20p10-of-rational real-type 16))
        (n-real (amc20p10-of-rational real-type n)))
    (implies
     (and
      (amc20p10-real-log-structure-p real-type)
      (natp n)
      (< 1 n)
      (equal
       (amc20p10-logb
        real-type
        two
        (amc20p10-logb real-type sixteen n-real))
       (amc20p10-logb
        real-type
        four
        (amc20p10-logb real-type four n-real))))
     (equal (amc20p10-digit-sum n) 13))))

(value-triple :itpeval-statement-checked)
:q
