;; Statement-only formalization of miniF2F artifact aime_1983_p3:
;; the product of the complete finite real zero set of
;; x^2 + 18*x + 30 - 2*sqrt(x^2 + 18*x + 45) is 20.
;; The source function is eliminated using its defining hypothesis.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no built-in first-class real field. An arbitrary carrier,
;; together with explicit ordered-field and principal-square-root laws,
;; represents the real quantities occurring in the source statement.

(defstub aime-1983-p3-real-p (real-type value) t)
(defstub aime-1983-p3-zero (real-type) t)
(defstub aime-1983-p3-one (real-type) t)
(defstub aime-1983-p3-add (real-type left right) t)
(defstub aime-1983-p3-mul (real-type left right) t)
(defstub aime-1983-p3-neg (real-type value) t)
(defstub aime-1983-p3-inv (real-type value) t)
(defstub aime-1983-p3-le (real-type left right) t)
(defstub aime-1983-p3-of-rational (real-type rational) t)
(defstub aime-1983-p3-sqrt (real-type value) t)

(defun aime-1983-p3-sub (real-type x y)
  (aime-1983-p3-add
   real-type x (aime-1983-p3-neg real-type y)))

(defun aime-1983-p3-square (real-type x)
  (aime-1983-p3-mul real-type x x))

(defun-sk aime-1983-p3-closure-laws-p (real-type)
  (forall (x y)
    (and
     (aime-1983-p3-real-p
      real-type (aime-1983-p3-zero real-type))
     (aime-1983-p3-real-p
      real-type (aime-1983-p3-one real-type))
     (implies
      (aime-1983-p3-real-p real-type x)
      (and
       (aime-1983-p3-real-p
        real-type (aime-1983-p3-neg real-type x))
       (aime-1983-p3-real-p
        real-type (aime-1983-p3-inv real-type x))
       (aime-1983-p3-real-p
        real-type (aime-1983-p3-sqrt real-type x))))
     (implies
      (and
       (aime-1983-p3-real-p real-type x)
       (aime-1983-p3-real-p real-type y))
      (and
       (aime-1983-p3-real-p
        real-type (aime-1983-p3-add real-type x y))
       (aime-1983-p3-real-p
        real-type (aime-1983-p3-mul real-type x y)))))))

(defun-sk aime-1983-p3-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (aime-1983-p3-real-p real-type x)
      (aime-1983-p3-real-p real-type y)
      (aime-1983-p3-real-p real-type z))
     (let ((zero (aime-1983-p3-zero real-type))
           (one (aime-1983-p3-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (aime-1983-p3-add real-type x y)
         (aime-1983-p3-add real-type y x))
        (equal
         (aime-1983-p3-add
          real-type
          (aime-1983-p3-add real-type x y)
          z)
         (aime-1983-p3-add
          real-type
          x
          (aime-1983-p3-add real-type y z)))
        (equal (aime-1983-p3-add real-type x zero) x)
        (equal
         (aime-1983-p3-add
          real-type x (aime-1983-p3-neg real-type x))
         zero)
        (equal
         (aime-1983-p3-mul real-type x y)
         (aime-1983-p3-mul real-type y x))
        (equal
         (aime-1983-p3-mul
          real-type
          (aime-1983-p3-mul real-type x y)
          z)
         (aime-1983-p3-mul
          real-type
          x
          (aime-1983-p3-mul real-type y z)))
        (equal (aime-1983-p3-mul real-type x one) x)
        (equal
         (aime-1983-p3-mul
          real-type
          x
          (aime-1983-p3-add real-type y z))
         (aime-1983-p3-add
          real-type
          (aime-1983-p3-mul real-type x y)
          (aime-1983-p3-mul real-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (aime-1983-p3-mul
           real-type x (aime-1983-p3-inv real-type x))
          one)))))))

(defun-sk aime-1983-p3-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (aime-1983-p3-real-p real-type x)
      (aime-1983-p3-real-p real-type y)
      (aime-1983-p3-real-p real-type z))
     (let ((zero (aime-1983-p3-zero real-type)))
       (and
        (aime-1983-p3-le real-type x x)
        (implies
         (and
          (aime-1983-p3-le real-type x y)
          (aime-1983-p3-le real-type y x))
         (equal x y))
        (implies
         (and
          (aime-1983-p3-le real-type x y)
          (aime-1983-p3-le real-type y z))
         (aime-1983-p3-le real-type x z))
        (or
         (aime-1983-p3-le real-type x y)
         (aime-1983-p3-le real-type y x))
        (implies
         (aime-1983-p3-le real-type x y)
         (aime-1983-p3-le
          real-type
          (aime-1983-p3-add real-type x z)
          (aime-1983-p3-add real-type y z)))
        (implies
         (and
          (aime-1983-p3-le real-type zero x)
          (aime-1983-p3-le real-type zero y))
         (aime-1983-p3-le
          real-type
          zero
          (aime-1983-p3-mul real-type x y))))))))

(defun-sk aime-1983-p3-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (aime-1983-p3-real-p
       real-type (aime-1983-p3-of-rational real-type p))
      (equal
       (aime-1983-p3-of-rational real-type 0)
       (aime-1983-p3-zero real-type))
      (equal
       (aime-1983-p3-of-rational real-type 1)
       (aime-1983-p3-one real-type))
      (equal
       (aime-1983-p3-of-rational real-type (+ p q))
       (aime-1983-p3-add
        real-type
        (aime-1983-p3-of-rational real-type p)
        (aime-1983-p3-of-rational real-type q)))
      (equal
       (aime-1983-p3-of-rational real-type (* p q))
       (aime-1983-p3-mul
        real-type
        (aime-1983-p3-of-rational real-type p)
        (aime-1983-p3-of-rational real-type q)))
      (equal
       (aime-1983-p3-of-rational real-type (- p))
       (aime-1983-p3-neg
        real-type
        (aime-1983-p3-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (aime-1983-p3-of-rational real-type p)
        (aime-1983-p3-of-rational real-type q)))
      (iff
       (<= p q)
       (aime-1983-p3-le
        real-type
        (aime-1983-p3-of-rational real-type p)
        (aime-1983-p3-of-rational real-type q)))))))

(defun-sk aime-1983-p3-square-root-laws-p (real-type)
  (forall (x)
    (implies
     (aime-1983-p3-real-p real-type x)
     (let ((zero (aime-1983-p3-zero real-type))
           (root (aime-1983-p3-sqrt real-type x)))
       (if (aime-1983-p3-le real-type zero x)
           (and
            (aime-1983-p3-le real-type zero root)
            (equal (aime-1983-p3-square real-type root) x))
         (equal root zero))))))

(defun aime-1983-p3-real-structure-p (real-type)
  (and
   (aime-1983-p3-closure-laws-p real-type)
   (aime-1983-p3-field-laws-p real-type)
   (aime-1983-p3-order-laws-p real-type)
   (aime-1983-p3-rational-laws-p real-type)
   (aime-1983-p3-square-root-laws-p real-type)))

(defun aime-1983-p3-expression (real-type x)
  (let* ((x-squared (aime-1983-p3-square real-type x))
         (eighteen-x
          (aime-1983-p3-mul
           real-type
           (aime-1983-p3-of-rational real-type 18)
           x))
         (radicand
          (aime-1983-p3-add
           real-type
           x-squared
           (aime-1983-p3-add
            real-type
            eighteen-x
            (aime-1983-p3-of-rational real-type 45))))
         (polynomial
          (aime-1983-p3-add
           real-type
           x-squared
           (aime-1983-p3-add
            real-type
            eighteen-x
            (aime-1983-p3-of-rational real-type 30)))))
    (aime-1983-p3-sub
     real-type
     polynomial
     (aime-1983-p3-mul
      real-type
      (aime-1983-p3-of-rational real-type 2)
      (aime-1983-p3-sqrt real-type radicand)))))

(defun aime-1983-p3-root-p (real-type x)
  (and
   (aime-1983-p3-real-p real-type x)
   (equal
    (aime-1983-p3-expression real-type x)
    (aime-1983-p3-zero real-type))))

;; A finite list represents the source Fintype. The biconditional makes it
;; the complete zero set, rather than an arbitrary collection of roots.
(defun-sk aime-1983-p3-complete-root-list-p (real-type roots)
  (forall (x)
    (iff
     (member-equal x roots)
     (aime-1983-p3-root-p real-type x))))

(defun aime-1983-p3-product (real-type roots)
  (if (endp roots)
      (aime-1983-p3-one real-type)
    (aime-1983-p3-mul
     real-type
     (car roots)
     (aime-1983-p3-product real-type (cdr roots)))))

(defun-sk aime-1983-p3-statement ()
  (forall (real-type roots)
    (implies
     (and
      (aime-1983-p3-real-structure-p real-type)
      (true-listp roots)
      (no-duplicatesp-equal roots)
      (aime-1983-p3-complete-root-list-p real-type roots))
     (equal
      (aime-1983-p3-product real-type roots)
      (aime-1983-p3-of-rational real-type 20)))))

(value-triple :itpeval-statement-checked)
:q
