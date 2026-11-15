;; Statement-only formalization of miniF2F artifact amc12_2000_p5:
;; for arbitrary real x and p, if x < 2 and |x - 2| = p, then
;; x - p = 2 - 2*p. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no built-in full real carrier. Only ordered additive-group
;; structure is needed here, so arbitrary carrier operations and their laws
;; are explicit theorem premises. This retains irrational source instances.

(defstub amc12-p5-real-p (real-type value) t)
(defstub amc12-p5-zero (real-type) t)
(defstub amc12-p5-add (real-type left right) t)
(defstub amc12-p5-neg (real-type value) t)
(defstub amc12-p5-le (real-type left right) t)
(defstub amc12-p5-of-rational (real-type rational) t)

(defun amc12-p5-sub (real-type x y)
  (amc12-p5-add
   real-type x (amc12-p5-neg real-type y)))

(defun amc12-p5-lt (real-type x y)
  (and
   (amc12-p5-le real-type x y)
   (not (equal x y))))

(defun amc12-p5-abs (real-type x)
  (if (amc12-p5-lt
       real-type x (amc12-p5-zero real-type))
      (amc12-p5-neg real-type x)
    x))

(defun-sk amc12-p5-closure-laws-p (real-type)
  (forall (x y)
    (and
     (amc12-p5-real-p
      real-type (amc12-p5-zero real-type))
     (implies
      (amc12-p5-real-p real-type x)
      (amc12-p5-real-p
       real-type (amc12-p5-neg real-type x)))
     (implies
      (and
       (amc12-p5-real-p real-type x)
       (amc12-p5-real-p real-type y))
      (amc12-p5-real-p
       real-type (amc12-p5-add real-type x y))))))

(defun-sk amc12-p5-additive-group-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc12-p5-real-p real-type x)
      (amc12-p5-real-p real-type y)
      (amc12-p5-real-p real-type z))
     (let ((zero (amc12-p5-zero real-type)))
       (and
        (equal
         (amc12-p5-add real-type x y)
         (amc12-p5-add real-type y x))
        (equal
         (amc12-p5-add
          real-type
          (amc12-p5-add real-type x y)
          z)
         (amc12-p5-add
          real-type
          x
          (amc12-p5-add real-type y z)))
        (equal (amc12-p5-add real-type x zero) x)
        (equal
         (amc12-p5-add
          real-type x (amc12-p5-neg real-type x))
         zero))))))

(defun-sk amc12-p5-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc12-p5-real-p real-type x)
      (amc12-p5-real-p real-type y)
      (amc12-p5-real-p real-type z))
     (and
      (amc12-p5-le real-type x x)
      (implies
       (and
        (amc12-p5-le real-type x y)
        (amc12-p5-le real-type y x))
       (equal x y))
      (implies
       (and
        (amc12-p5-le real-type x y)
        (amc12-p5-le real-type y z))
       (amc12-p5-le real-type x z))
      (or
       (amc12-p5-le real-type x y)
       (amc12-p5-le real-type y x))
      (implies
       (amc12-p5-le real-type x y)
       (amc12-p5-le
        real-type
        (amc12-p5-add real-type x z)
        (amc12-p5-add real-type y z)))))))

(defun-sk amc12-p5-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (amc12-p5-real-p
       real-type (amc12-p5-of-rational real-type p))
      (equal
       (amc12-p5-of-rational real-type 0)
       (amc12-p5-zero real-type))
      (equal
       (amc12-p5-of-rational real-type (+ p q))
       (amc12-p5-add
        real-type
        (amc12-p5-of-rational real-type p)
        (amc12-p5-of-rational real-type q)))
      (equal
       (amc12-p5-of-rational real-type (- p))
       (amc12-p5-neg
        real-type
        (amc12-p5-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (amc12-p5-of-rational real-type p)
        (amc12-p5-of-rational real-type q)))
      (iff
       (<= p q)
       (amc12-p5-le
        real-type
        (amc12-p5-of-rational real-type p)
        (amc12-p5-of-rational real-type q)))))))

(defun amc12-p5-real-structure-p (real-type)
  (and
   (amc12-p5-closure-laws-p real-type)
   (amc12-p5-additive-group-laws-p real-type)
   (amc12-p5-order-laws-p real-type)
   (amc12-p5-rational-laws-p real-type)))

(defun-sk amc12-2000-p5-statement ()
  (forall (real-type x p)
    (implies
     (and
      (amc12-p5-real-structure-p real-type)
      (amc12-p5-real-p real-type x)
      (amc12-p5-real-p real-type p)
      (amc12-p5-lt
       real-type
       x
       (amc12-p5-of-rational real-type 2))
      (equal
       (amc12-p5-abs
        real-type
        (amc12-p5-sub
         real-type
         x
         (amc12-p5-of-rational real-type 2)))
       p))
     (equal
      (amc12-p5-sub real-type x p)
      (amc12-p5-sub
       real-type
       (amc12-p5-of-rational real-type 2)
       (amc12-p5-add real-type p p))))))

(value-triple :itpeval-statement-checked)
:q
