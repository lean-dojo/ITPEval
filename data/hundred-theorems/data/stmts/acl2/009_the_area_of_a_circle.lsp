;; Statement-only formalization of Hundred Theorems artifact 009,
;; "The Area of a Circle." The outer area of every open Euclidean disc of
;; nonnegative real radius is pi times the square of the radius. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; ACL2's built-in numbers are rational, so the reals are represented by an
;; explicit Archimedean real-closed ordered field. Pi is independently fixed
;; as the limit of the Leibniz series.

(defstub ht009-carrier (x) t)
(defstub ht009-add-op (x y) t)
(defstub ht009-multiply-op (x y) t)
(defstub ht009-negate-op (x) t)
(defstub ht009-inverse-op (x) t)
(defstub ht009-less-op (x y) t)
(defstub ht009-zero () t)
(defstub ht009-one () t)
(defstub ht009-pi () t)

(defun ht009-member-p (x)
  (if (ht009-carrier x) t nil))

(defun ht009-add (x y)
  (ht009-add-op x y))

(defun ht009-multiply (x y)
  (ht009-multiply-op x y))

(defun ht009-negate (x)
  (ht009-negate-op x))

(defun ht009-inverse (x)
  (ht009-inverse-op x))

(defun ht009-subtract (x y)
  (ht009-add x (ht009-negate y)))

(defun ht009-divide (x y)
  (ht009-multiply x (ht009-inverse y)))

(defun ht009-less (x y)
  (if (ht009-less-op x y) t nil))

(defun ht009-less-or-equal (x y)
  (or
   (equal x y)
   (ht009-less x y)))

(defun ht009-positive-p (x)
  (and
   (ht009-member-p x)
   (ht009-less (ht009-zero) x)))

(defun ht009-nonnegative-p (x)
  (and
   (ht009-member-p x)
   (not (ht009-less x (ht009-zero)))))

(defun ht009-square (x)
  (ht009-multiply x x))

(defun ht009-absolute (x)
  (if (ht009-less x (ht009-zero))
      (ht009-negate x)
    x))

(defun ht009-natural (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (ht009-zero)
    (ht009-add
     (ht009-one)
     (ht009-natural (1- n)))))

(defun-sk ht009-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (ht009-member-p x)
      (ht009-member-p y)
      (ht009-member-p z))
     (and
      (ht009-member-p (ht009-add x y))
      (ht009-member-p (ht009-multiply x y))
      (ht009-member-p (ht009-negate x))
      (ht009-member-p (ht009-inverse x))
      (equal (ht009-add (ht009-add x y) z)
             (ht009-add x (ht009-add y z)))
      (equal (ht009-add x y)
             (ht009-add y x))
      (equal (ht009-add x (ht009-zero)) x)
      (equal
       (ht009-add x (ht009-negate x))
       (ht009-zero))
      (equal
       (ht009-multiply (ht009-multiply x y) z)
       (ht009-multiply x (ht009-multiply y z)))
      (equal
       (ht009-multiply x y)
       (ht009-multiply y x))
      (equal
       (ht009-multiply x (ht009-one))
       x)
      (equal
       (ht009-multiply x (ht009-add y z))
       (ht009-add
        (ht009-multiply x y)
        (ht009-multiply x z)))
      (implies
       (equal x (ht009-zero))
       (equal (ht009-inverse x) (ht009-zero)))
      (implies
       (not (equal x (ht009-zero)))
       (equal
        (ht009-multiply x (ht009-inverse x))
        (ht009-one)))))))

(defun-sk ht009-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (ht009-member-p x)
      (ht009-member-p y)
      (ht009-member-p z))
     (and
      (not (ht009-less x x))
      (or
       (equal x y)
       (ht009-less x y)
       (ht009-less y x))
      (implies
       (and
        (ht009-less x y)
        (ht009-less y z))
       (ht009-less x z))
      (implies
       (ht009-less x y)
       (ht009-less
        (ht009-add x z)
        (ht009-add y z)))
      (implies
       (and
        (ht009-less (ht009-zero) x)
        (ht009-less (ht009-zero) y))
       (ht009-less
        (ht009-zero)
        (ht009-multiply x y)))))))

(defun ht009-field-list-p (values)
  (if (consp values)
      (and
       (ht009-member-p (car values))
       (ht009-field-list-p (cdr values)))
    (equal values nil)))

(defun ht009-polynomial-value (coefficients x)
  (if (consp coefficients)
      (ht009-add
       (car coefficients)
       (ht009-multiply
        x
        (ht009-polynomial-value (cdr coefficients) x)))
    (ht009-zero)))

(defun ht009-odd-degree-polynomial-p (coefficients)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (ht009-field-list-p coefficients)
   (evenp (len coefficients))
   (not
    (equal
     (car (last coefficients))
     (ht009-zero)))))

(defun-sk ht009-square-root-exists-p (x)
  (exists (root)
    (and
     (ht009-member-p root)
     (equal (ht009-square root) x))))

(defun-sk ht009-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (ht009-member-p root)
     (equal
      (ht009-polynomial-value coefficients root)
      (ht009-zero)))))

(defun-sk ht009-real-closure-laws-p ()
  (forall (x coefficients)
    (and
     (implies
      (ht009-nonnegative-p x)
      (ht009-square-root-exists-p x))
     (implies
      (ht009-odd-degree-polynomial-p coefficients)
      (ht009-polynomial-root-exists-p coefficients)))))

(defun-sk ht009-natural-bound-exists-p (x)
  (exists (n)
    (and
     (natp n)
     (ht009-less x (ht009-natural n)))))

(defun-sk ht009-archimedean-law-p ()
  (forall (x)
    (implies
     (ht009-member-p x)
     (ht009-natural-bound-exists-p x))))

(defun ht009-real-scalar-context-p ()
  (and
   (ht009-member-p (ht009-zero))
   (ht009-member-p (ht009-one))
   (not (equal (ht009-zero) (ht009-one)))
   (ht009-less (ht009-zero) (ht009-one))
   (ht009-field-laws-p)
   (ht009-order-laws-p)
   (ht009-real-closure-laws-p)
   (ht009-archimedean-law-p)))

;; The nth prefix is four times
;;   1 - 1/3 + 1/5 - ... + (-1)^(n-1)/(2n-1).

(defun ht009-leibniz-term (index)
  (let* ((denominator
          (ht009-natural (+ (* 2 index) 1)))
         (unsigned
          (ht009-divide (ht009-one) denominator)))
    (if (equal (mod index 2) 0)
        unsigned
      (ht009-negate unsigned))))

(defun ht009-leibniz-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (ht009-zero)
    (ht009-add
     (ht009-leibniz-prefix (1- terms))
     (ht009-leibniz-term (1- terms)))))

(defun ht009-pi-prefix (terms)
  (ht009-multiply
   (ht009-natural 4)
   (ht009-leibniz-prefix terms)))

(defun-sk ht009-pi-tail-p (epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (ht009-less
      (ht009-absolute
       (ht009-subtract
        (ht009-pi-prefix terms)
        (ht009-pi)))
      epsilon))))

(defun-sk ht009-pi-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht009-pi-tail-p epsilon cutoff))))

(defun-sk ht009-pi-value-p ()
  (forall (epsilon)
    (implies
     (ht009-positive-p epsilon)
     (ht009-pi-cutoff-exists-p epsilon))))

(defun ht009-exact-pi-p ()
  (and
   (ht009-member-p (ht009-pi))
   (ht009-positive-p (ht009-pi))
   (ht009-pi-value-p)))

;; A box is the proper list (left right bottom top). Area is characterized as
;; outer Jordan area: a value is below every finite open-box cover and can be
;; approached arbitrarily closely by such covers. For a disc this equals its
;; Lebesgue measure, while avoiding an under-specified abstract sigma-algebra.

(defun ht009-open-disc-member-p
    (center-x center-y radius x y)
  (ht009-less
   (ht009-add
    (ht009-square (ht009-subtract x center-x))
    (ht009-square (ht009-subtract y center-y)))
   (ht009-square radius)))

(defun ht009-box-p (box)
  (and
   (true-listp box)
   (equal (len box) 4)
   (ht009-member-p (nth 0 box))
   (ht009-member-p (nth 1 box))
   (ht009-member-p (nth 2 box))
   (ht009-member-p (nth 3 box))
   (ht009-less (nth 0 box) (nth 1 box))
   (ht009-less (nth 2 box) (nth 3 box))))

(defun ht009-point-in-open-box-p (x y box)
  (and
   (ht009-less (nth 0 box) x)
   (ht009-less x (nth 1 box))
   (ht009-less (nth 2 box) y)
   (ht009-less y (nth 3 box))))

(defun ht009-box-area (box)
  (ht009-multiply
   (ht009-subtract (nth 1 box) (nth 0 box))
   (ht009-subtract (nth 3 box) (nth 2 box))))

(defun ht009-box-list-p (boxes)
  (if (consp boxes)
      (and
       (ht009-box-p (car boxes))
       (ht009-box-list-p (cdr boxes)))
    (equal boxes nil)))

(defun ht009-point-covered-p (x y boxes)
  (if (consp boxes)
      (or
       (ht009-point-in-open-box-p x y (car boxes))
       (ht009-point-covered-p x y (cdr boxes)))
    nil))

(defun ht009-cover-total-area (boxes)
  (if (consp boxes)
      (ht009-add
       (ht009-box-area (car boxes))
       (ht009-cover-total-area (cdr boxes)))
    (ht009-zero)))

(defun-sk ht009-boxes-cover-disc-p
    (center-x center-y radius boxes)
  (forall (x y)
    (implies
     (and
      (ht009-member-p x)
      (ht009-member-p y)
      (ht009-open-disc-member-p
       center-x center-y radius x y))
     (ht009-point-covered-p x y boxes))))

(defun ht009-valid-disc-cover-p
    (center-x center-y radius boxes)
  (and
   (true-listp boxes)
   (ht009-box-list-p boxes)
   (ht009-boxes-cover-disc-p
    center-x center-y radius boxes)))

(defun-sk ht009-area-below-every-cover-p
    (center-x center-y radius area)
  (forall (boxes)
    (implies
     (ht009-valid-disc-cover-p
      center-x center-y radius boxes)
     (ht009-less-or-equal
      area
      (ht009-cover-total-area boxes)))))

(defun-sk ht009-close-cover-exists-p
    (center-x center-y radius area epsilon)
  (exists (boxes)
    (and
     (ht009-valid-disc-cover-p
      center-x center-y radius boxes)
     (ht009-less
      (ht009-cover-total-area boxes)
      (ht009-add area epsilon)))))

(defun-sk ht009-arbitrarily-close-covers-p
    (center-x center-y radius area)
  (forall (epsilon)
    (implies
     (ht009-positive-p epsilon)
     (ht009-close-cover-exists-p
      center-x center-y radius area epsilon))))

(defun ht009-is-disc-area-p
    (center-x center-y radius area)
  (and
   (ht009-nonnegative-p area)
   (ht009-area-below-every-cover-p
    center-x center-y radius area)
   (ht009-arbitrarily-close-covers-p
    center-x center-y radius area)))

(defun-sk hundred-theorems-009-area-of-a-circle-statement ()
  (forall (center-x center-y radius)
    (implies
     (and
      (ht009-real-scalar-context-p)
      (ht009-exact-pi-p)
      (ht009-member-p center-x)
      (ht009-member-p center-y)
      (ht009-nonnegative-p radius))
     (ht009-is-disc-area-p
      center-x
      center-y
      radius
      (ht009-multiply
       (ht009-pi)
       (ht009-square radius))))))

(value-triple :itpeval-statement-checked)
:q
