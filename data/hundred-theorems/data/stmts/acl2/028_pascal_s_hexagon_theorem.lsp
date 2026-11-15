;; Statement-only formalization of hundred-theorems__acl2__028,
;; "Pascal's Hexagon Theorem": six nondegenerate points on an affine conic
;; determine three collinear opposite-side intersections. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no native abstract field type. These conservative function symbols
;; represent an arbitrary scalar carrier and its operations. The explicit field
;; hypotheses below expose all algebraic assumptions; no geometric conclusion
;; is installed as an axiom. Pascal's theorem is purely field-theoretic, so
;; stating it over an arbitrary commutative field is a conservative
;; generalization of the real affine-plane source.

(defstub ht028-scalar-member-p (scalar-type value) t)
(defstub ht028-zero (scalar-type) t)
(defstub ht028-one (scalar-type) t)
(defstub ht028-add (scalar-type left right) t)
(defstub ht028-multiply (scalar-type left right) t)
(defstub ht028-negate (scalar-type value) t)
(defstub ht028-inverse (scalar-type value) t)

(defun-sk ht028-field-laws-p (scalar-type)
  (forall (x y z)
    (implies
     (and
      (ht028-scalar-member-p scalar-type x)
      (ht028-scalar-member-p scalar-type y)
      (ht028-scalar-member-p scalar-type z))
     (let ((zero (ht028-zero scalar-type))
           (one (ht028-one scalar-type)))
       (and
        (ht028-scalar-member-p
         scalar-type (ht028-add scalar-type x y))
        (ht028-scalar-member-p
         scalar-type (ht028-multiply scalar-type x y))
        (ht028-scalar-member-p
         scalar-type (ht028-negate scalar-type x))
        (ht028-scalar-member-p
         scalar-type (ht028-inverse scalar-type x))

        (equal
         (ht028-add scalar-type x y)
         (ht028-add scalar-type y x))
        (equal
         (ht028-add
          scalar-type (ht028-add scalar-type x y) z)
         (ht028-add
          scalar-type x (ht028-add scalar-type y z)))
        (equal (ht028-add scalar-type x zero) x)
        (equal
         (ht028-add scalar-type x (ht028-negate scalar-type x))
         zero)

        (equal
         (ht028-multiply scalar-type x y)
         (ht028-multiply scalar-type y x))
        (equal
         (ht028-multiply
          scalar-type (ht028-multiply scalar-type x y) z)
         (ht028-multiply
          scalar-type x (ht028-multiply scalar-type y z)))
        (equal (ht028-multiply scalar-type x one) x)
        (equal (ht028-multiply scalar-type x zero) zero)
        (equal
         (ht028-multiply
          scalar-type x (ht028-add scalar-type y z))
         (ht028-add
          scalar-type
          (ht028-multiply scalar-type x y)
          (ht028-multiply scalar-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (ht028-multiply
           scalar-type x (ht028-inverse scalar-type x))
          one)))))))

(defun ht028-field-p (scalar-type)
  (and
   (ht028-scalar-member-p scalar-type (ht028-zero scalar-type))
   (ht028-scalar-member-p scalar-type (ht028-one scalar-type))
   (not
    (equal
     (ht028-zero scalar-type)
     (ht028-one scalar-type)))
   (ht028-field-laws-p scalar-type)))

;; Points are pairs of scalar coordinates. The source's type discipline becomes
;; explicit carrier checks in ACL2's untyped logic.

(defun ht028-point-p (scalar-type point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (ht028-scalar-member-p scalar-type (nth 0 point))
   (ht028-scalar-member-p scalar-type (nth 1 point))))

(defun ht028-point-x (point)
  (nth 0 point))

(defun ht028-point-y (point)
  (nth 1 point))

(defun ht028-subtract (scalar-type left right)
  (ht028-add scalar-type left (ht028-negate scalar-type right)))

(defun ht028-square (scalar-type value)
  (ht028-multiply scalar-type value value))

;; The determinant criterion is exactly affine collinearity.

(defun ht028-collinear-p (scalar-type first second third)
  (equal
   (ht028-multiply
    scalar-type
    (ht028-subtract
     scalar-type
     (ht028-point-x second)
     (ht028-point-x first))
    (ht028-subtract
     scalar-type
     (ht028-point-y third)
     (ht028-point-y first)))
   (ht028-multiply
    scalar-type
    (ht028-subtract
     scalar-type
     (ht028-point-y second)
     (ht028-point-y first))
    (ht028-subtract
     scalar-type
     (ht028-point-x third)
     (ht028-point-x first)))))

;; Evaluation of a*x^2 + b*y^2 + c*x*y + d*x + e*y + f.

(defun ht028-quadratic-value
    (scalar-type a b c d e f point)
  (ht028-add
   scalar-type
   (ht028-add
    scalar-type
    (ht028-add
     scalar-type
     (ht028-multiply
      scalar-type a
      (ht028-square scalar-type (ht028-point-x point)))
     (ht028-multiply
      scalar-type b
      (ht028-square scalar-type (ht028-point-y point))))
    (ht028-multiply
     scalar-type c
     (ht028-multiply
      scalar-type
      (ht028-point-x point)
      (ht028-point-y point))))
   (ht028-add
    scalar-type
    (ht028-multiply scalar-type d (ht028-point-x point))
    (ht028-add
     scalar-type
     (ht028-multiply scalar-type e (ht028-point-y point))
     f))))

(defun ht028-on-conic-p
    (scalar-type a b c d e f point)
  (equal
   (ht028-quadratic-value scalar-type a b c d e f point)
   (ht028-zero scalar-type)))

(defun ht028-nonzero-conic-p (scalar-type a b c d e f)
  (not
   (and
    (equal a (ht028-zero scalar-type))
    (equal b (ht028-zero scalar-type))
    (equal c (ht028-zero scalar-type))
    (equal d (ht028-zero scalar-type))
    (equal e (ht028-zero scalar-type))
    (equal f (ht028-zero scalar-type)))))

(defun ht028-pairwise-distinct-six-p
    (p1 p2 p3 p4 p5 p6)
  (and
   (not (equal p1 p2))
   (not (equal p1 p3))
   (not (equal p1 p4))
   (not (equal p1 p5))
   (not (equal p1 p6))
   (not (equal p2 p3))
   (not (equal p2 p4))
   (not (equal p2 p5))
   (not (equal p2 p6))
   (not (equal p3 p4))
   (not (equal p3 p5))
   (not (equal p3 p6))
   (not (equal p4 p5))
   (not (equal p4 p6))
   (not (equal p5 p6))))

;; No triple meeting both alternating vertex classes {p1,p3,p5} and
;; {p2,p4,p6} is collinear. This is the source's general-position condition,
;; not a replacement for the conic hypothesis.

(defun ht028-pascal-nondegenerate-p
    (scalar-type p1 p2 p3 p4 p5 p6)
  (and
   (ht028-pairwise-distinct-six-p p1 p2 p3 p4 p5 p6)
   (not (ht028-collinear-p scalar-type p1 p3 p2))
   (not (ht028-collinear-p scalar-type p1 p3 p4))
   (not (ht028-collinear-p scalar-type p1 p3 p6))
   (not (ht028-collinear-p scalar-type p1 p5 p2))
   (not (ht028-collinear-p scalar-type p1 p5 p4))
   (not (ht028-collinear-p scalar-type p1 p5 p6))
   (not (ht028-collinear-p scalar-type p3 p5 p2))
   (not (ht028-collinear-p scalar-type p3 p5 p4))
   (not (ht028-collinear-p scalar-type p3 p5 p6))
   (not (ht028-collinear-p scalar-type p2 p4 p1))
   (not (ht028-collinear-p scalar-type p2 p4 p3))
   (not (ht028-collinear-p scalar-type p2 p4 p5))
   (not (ht028-collinear-p scalar-type p2 p6 p1))
   (not (ht028-collinear-p scalar-type p2 p6 p3))
   (not (ht028-collinear-p scalar-type p2 p6 p5))
   (not (ht028-collinear-p scalar-type p4 p6 p1))
   (not (ht028-collinear-p scalar-type p4 p6 p3))
   (not (ht028-collinear-p scalar-type p4 p6 p5))))

(defun ht028-pascal-intersections-p
    (scalar-type p1 p2 p3 p4 p5 p6 i1 i2 i3)
  (and
   (ht028-collinear-p scalar-type i1 p1 p2)
   (ht028-collinear-p scalar-type i1 p4 p5)
   (ht028-collinear-p scalar-type i2 p2 p3)
   (ht028-collinear-p scalar-type i2 p5 p6)
   (ht028-collinear-p scalar-type i3 p3 p4)
   (ht028-collinear-p scalar-type i3 p6 p1)))

(defun-sk hundred-theorems-028-pascal-hexagon-statement
    (scalar-type)
  (forall (a b c d e f p1 p2 p3 p4 p5 p6 i1 i2 i3)
    (implies
     (and
      (ht028-field-p scalar-type)
      (ht028-scalar-member-p scalar-type a)
      (ht028-scalar-member-p scalar-type b)
      (ht028-scalar-member-p scalar-type c)
      (ht028-scalar-member-p scalar-type d)
      (ht028-scalar-member-p scalar-type e)
      (ht028-scalar-member-p scalar-type f)
      (ht028-point-p scalar-type p1)
      (ht028-point-p scalar-type p2)
      (ht028-point-p scalar-type p3)
      (ht028-point-p scalar-type p4)
      (ht028-point-p scalar-type p5)
      (ht028-point-p scalar-type p6)
      (ht028-point-p scalar-type i1)
      (ht028-point-p scalar-type i2)
      (ht028-point-p scalar-type i3)
      (ht028-nonzero-conic-p scalar-type a b c d e f)
      (ht028-pascal-nondegenerate-p
       scalar-type p1 p2 p3 p4 p5 p6)
      (ht028-on-conic-p scalar-type a b c d e f p1)
      (ht028-on-conic-p scalar-type a b c d e f p2)
      (ht028-on-conic-p scalar-type a b c d e f p3)
      (ht028-on-conic-p scalar-type a b c d e f p4)
      (ht028-on-conic-p scalar-type a b c d e f p5)
      (ht028-on-conic-p scalar-type a b c d e f p6)
      (ht028-pascal-intersections-p
       scalar-type p1 p2 p3 p4 p5 p6 i1 i2 i3))
     (ht028-collinear-p scalar-type i1 i2 i3))))

(value-triple :itpeval-statement-checked)
:q
