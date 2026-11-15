;; Statement-only formalization of miniF2F artifact
;; algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778: for every real r, if
;; its real cube root c satisfies c + 1/c = 3, then
;; r^3 + 1/r^3 = 5778. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no built-in first-class real field. The arbitrary carrier below
;; preserves the source's full real domain through explicit ordered-field and
;; rational-embedding laws. In an ordered field a cube root is unique, so the
;; witness c with c^3 = r is equivalent to the source's fixed real cube root;
;; it does not select or precompute either algebraic solution.

(defstub cubrtr-real-p (real-type value) t)
(defstub cubrtr-zero (real-type) t)
(defstub cubrtr-one (real-type) t)
(defstub cubrtr-add (real-type left right) t)
(defstub cubrtr-mul (real-type left right) t)
(defstub cubrtr-neg (real-type value) t)
(defstub cubrtr-inv (real-type value) t)
(defstub cubrtr-le (real-type left right) t)
(defstub cubrtr-of-rational (real-type rational) t)

(defun cubrtr-cube (real-type x)
  (cubrtr-mul
   real-type
   x
   (cubrtr-mul real-type x x)))

(defun-sk cubrtr-closure-laws-p (real-type)
  (forall (x y)
    (and
     (cubrtr-real-p real-type (cubrtr-zero real-type))
     (cubrtr-real-p real-type (cubrtr-one real-type))
     (implies
      (cubrtr-real-p real-type x)
      (and
       (cubrtr-real-p real-type (cubrtr-neg real-type x))
       (cubrtr-real-p real-type (cubrtr-inv real-type x))))
     (implies
      (and
       (cubrtr-real-p real-type x)
       (cubrtr-real-p real-type y))
      (and
       (cubrtr-real-p real-type (cubrtr-add real-type x y))
       (cubrtr-real-p real-type (cubrtr-mul real-type x y)))))))

(defun-sk cubrtr-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (cubrtr-real-p real-type x)
      (cubrtr-real-p real-type y)
      (cubrtr-real-p real-type z))
     (let ((zero (cubrtr-zero real-type))
           (one (cubrtr-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (cubrtr-add real-type x y)
         (cubrtr-add real-type y x))
        (equal
         (cubrtr-add real-type (cubrtr-add real-type x y) z)
         (cubrtr-add real-type x (cubrtr-add real-type y z)))
        (equal (cubrtr-add real-type x zero) x)
        (equal
         (cubrtr-add real-type x (cubrtr-neg real-type x))
         zero)
        (equal
         (cubrtr-mul real-type x y)
         (cubrtr-mul real-type y x))
        (equal
         (cubrtr-mul real-type (cubrtr-mul real-type x y) z)
         (cubrtr-mul real-type x (cubrtr-mul real-type y z)))
        (equal (cubrtr-mul real-type x one) x)
        (equal
         (cubrtr-mul
          real-type
          x
          (cubrtr-add real-type y z))
         (cubrtr-add
          real-type
          (cubrtr-mul real-type x y)
          (cubrtr-mul real-type x z)))
        (equal (cubrtr-inv real-type zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (cubrtr-mul real-type x (cubrtr-inv real-type x))
          one)))))))

(defun-sk cubrtr-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (cubrtr-real-p real-type x)
      (cubrtr-real-p real-type y)
      (cubrtr-real-p real-type z))
     (let ((zero (cubrtr-zero real-type)))
       (and
        (cubrtr-le real-type x x)
        (implies
         (and
          (cubrtr-le real-type x y)
          (cubrtr-le real-type y x))
         (equal x y))
        (implies
         (and
          (cubrtr-le real-type x y)
          (cubrtr-le real-type y z))
         (cubrtr-le real-type x z))
        (or
         (cubrtr-le real-type x y)
         (cubrtr-le real-type y x))
        (implies
         (cubrtr-le real-type x y)
         (cubrtr-le
          real-type
          (cubrtr-add real-type x z)
          (cubrtr-add real-type y z)))
        (implies
         (and
          (cubrtr-le real-type zero x)
          (cubrtr-le real-type zero y))
         (cubrtr-le
          real-type
          zero
          (cubrtr-mul real-type x y))))))))

(defun-sk cubrtr-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (cubrtr-real-p
       real-type (cubrtr-of-rational real-type p))
      (equal
       (cubrtr-of-rational real-type 0)
       (cubrtr-zero real-type))
      (equal
       (cubrtr-of-rational real-type 1)
       (cubrtr-one real-type))
      (equal
       (cubrtr-of-rational real-type (+ p q))
       (cubrtr-add
        real-type
        (cubrtr-of-rational real-type p)
        (cubrtr-of-rational real-type q)))
      (equal
       (cubrtr-of-rational real-type (* p q))
       (cubrtr-mul
        real-type
        (cubrtr-of-rational real-type p)
        (cubrtr-of-rational real-type q)))
      (equal
       (cubrtr-of-rational real-type (- p))
       (cubrtr-neg
        real-type
        (cubrtr-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (cubrtr-of-rational real-type p)
        (cubrtr-of-rational real-type q)))
      (iff
       (<= p q)
       (cubrtr-le
        real-type
        (cubrtr-of-rational real-type p)
        (cubrtr-of-rational real-type q)))))))

(defun cubrtr-real-structure-p (real-type)
  (and
   (cubrtr-closure-laws-p real-type)
   (cubrtr-field-laws-p real-type)
   (cubrtr-order-laws-p real-type)
   (cubrtr-rational-laws-p real-type)))

(defun-sk algebra-cubrtrp1oncubrtreq3-rcubp1onrcubeq5778-statement ()
  (forall (real-type r cube-root)
    (implies
     (and
      (cubrtr-real-structure-p real-type)
      (cubrtr-real-p real-type r)
      (cubrtr-real-p real-type cube-root)
      (equal
       (cubrtr-cube real-type cube-root)
       r)
      (equal
       (cubrtr-add
        real-type
        cube-root
        (cubrtr-inv real-type cube-root))
       (cubrtr-of-rational real-type 3)))
     (equal
      (cubrtr-add
       real-type
       (cubrtr-cube real-type r)
       (cubrtr-inv
        real-type
        (cubrtr-cube real-type r)))
      (cubrtr-of-rational real-type 5778)))))

(value-triple :itpeval-statement-checked)
:q
