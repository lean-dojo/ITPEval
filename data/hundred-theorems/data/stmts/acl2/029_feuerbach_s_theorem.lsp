;; Statement-only formalization of Hundred Theorems artifact 029,
;; "Feuerbach's Theorem." The nine-point circle of a noncollinear real
;; triangle is tangent to each in/excircle specified by perpendicular contacts
;; with the three side lines. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A real-closed ordered field is enough for this coordinate theorem. Its
;; first-order algebraic sentences have the same truth value as over the real
;; numbers, while avoiding ACL2's built-in rational-number specialization.

(defstub ht029-carrier (x) t)
(defstub ht029-add-op (x y) t)
(defstub ht029-multiply-op (x y) t)
(defstub ht029-negate-op (x) t)
(defstub ht029-inverse-op (x) t)
(defstub ht029-less-op (x y) t)

(defun ht029-member-p (x)
  (if (ht029-carrier x) t nil))

(defun ht029-add (x y)
  (ht029-add-op x y))

(defun ht029-multiply (x y)
  (ht029-multiply-op x y))

(defun ht029-negate (x)
  (ht029-negate-op x))

(defun ht029-inverse (x)
  (ht029-inverse-op x))

(defun ht029-subtract (x y)
  (ht029-add x (ht029-negate y)))

(defun ht029-less (x y)
  (if (ht029-less-op x y) t nil))

(defun ht029-square (x)
  (ht029-multiply x x))

(defun-sk ht029-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht029-member-p x)
      (ht029-member-p y)
      (ht029-member-p z))
     (and
      (ht029-member-p (ht029-add x y))
      (ht029-member-p (ht029-multiply x y))
      (ht029-member-p (ht029-negate x))
      (ht029-member-p (ht029-inverse x))
      (equal (ht029-add (ht029-add x y) z)
             (ht029-add x (ht029-add y z)))
      (equal (ht029-add x y)
             (ht029-add y x))
      (equal (ht029-add x zero) x)
      (equal (ht029-add x (ht029-negate x)) zero)
      (equal (ht029-multiply (ht029-multiply x y) z)
             (ht029-multiply x (ht029-multiply y z)))
      (equal (ht029-multiply x y)
             (ht029-multiply y x))
      (equal (ht029-multiply x one) x)
      (equal
       (ht029-multiply x (ht029-add y z))
       (ht029-add
        (ht029-multiply x y)
        (ht029-multiply x z)))
      (implies
       (not (equal x zero))
       (equal
        (ht029-multiply x (ht029-inverse x))
        one))))))

(defun-sk ht029-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht029-member-p x)
      (ht029-member-p y)
      (ht029-member-p z))
     (and
      (not (ht029-less x x))
      (or
       (equal x y)
       (ht029-less x y)
       (ht029-less y x))
      (implies
       (and
        (ht029-less x y)
        (ht029-less y z))
       (ht029-less x z))
      (implies
       (ht029-less x y)
       (ht029-less
        (ht029-add x z)
        (ht029-add y z)))
      (implies
       (and
        (ht029-less zero x)
        (ht029-less zero y))
       (ht029-less zero (ht029-multiply x y)))))))

(defun ht029-field-list-p (values)
  (if (consp values)
      (and
       (ht029-member-p (car values))
       (ht029-field-list-p (cdr values)))
    (equal values nil)))

;; Coefficients are stored in ascending order. Real closedness is expressed by
;; the standard characterization: nonnegative elements have square roots and
;; every odd-degree polynomial has a root.
(defun ht029-polynomial-value (coefficients x zero)
  (if (consp coefficients)
      (ht029-add
       (car coefficients)
       (ht029-multiply
        x
        (ht029-polynomial-value (cdr coefficients) x zero)))
    zero))

(defun ht029-odd-degree-polynomial-p (coefficients zero)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (ht029-field-list-p coefficients)
   (evenp (len coefficients))
   (not (equal (car (last coefficients)) zero))))

(defun-sk ht029-has-square-root-p (x zero)
  (exists (root)
    (and
     (ht029-member-p root)
     (equal (ht029-square root) x))))

(defun-sk ht029-has-polynomial-root-p (coefficients zero)
  (exists (root)
    (and
     (ht029-member-p root)
     (equal
      (ht029-polynomial-value coefficients root zero)
      zero))))

(defun-sk ht029-real-closure-laws-p (zero)
  (forall (x coefficients)
    (and
     (implies
      (and
       (ht029-member-p x)
       (not (ht029-less x zero)))
      (ht029-has-square-root-p x zero))
     (implies
      (ht029-odd-degree-polynomial-p coefficients zero)
      (ht029-has-polynomial-root-p coefficients zero)))))

(defun ht029-real-scalar-context-p (zero one)
  (and
   (ht029-member-p zero)
   (ht029-member-p one)
   (not (equal zero one))
   (ht029-less zero one)
   (ht029-field-laws-p zero one)
   (ht029-order-laws-p zero)
   (ht029-real-closure-laws-p zero)))

;; Points are represented by dotted coordinate pairs (x . y).
(defun ht029-point-p (point)
  (and
   (consp point)
   (ht029-member-p (car point))
   (ht029-member-p (cdr point))))

(defun ht029-distance-squared (first second)
  (let ((dx (ht029-subtract (car second) (car first)))
        (dy (ht029-subtract (cdr second) (cdr first))))
    (ht029-add
     (ht029-square dx)
     (ht029-square dy))))

(defun ht029-midpoint-p (first second midpoint one)
  (let ((two (ht029-add one one)))
    (and
     (equal
      (ht029-multiply two (car midpoint))
      (ht029-add (car first) (car second)))
     (equal
      (ht029-multiply two (cdr midpoint))
      (ht029-add (cdr first) (cdr second))))))

(defun ht029-collinear-p (first second third)
  (equal
   (ht029-multiply
    (ht029-subtract (car first) (car second))
    (ht029-subtract (cdr third) (cdr second)))
   (ht029-multiply
    (ht029-subtract (cdr first) (cdr second))
    (ht029-subtract (car third) (car second)))))

(defun ht029-orthogonal-p
    (first-start first-end second-start second-end zero)
  (equal
   (ht029-add
    (ht029-multiply
     (ht029-subtract (car first-start) (car first-end))
     (ht029-subtract (car second-start) (car second-end)))
    (ht029-multiply
     (ht029-subtract (cdr first-start) (cdr first-end))
     (ht029-subtract (cdr second-start) (cdr second-end))))
   zero))

(defun ht029-nonnegative-p (zero value)
  (and
   (ht029-member-p value)
   (not (ht029-less value zero))))

(defun ht029-on-circle-p (center radius point zero)
  (and
   (ht029-point-p center)
   (ht029-point-p point)
   (ht029-nonnegative-p zero radius)
   (equal
    (ht029-distance-squared center point)
    (ht029-square radius))))

;; For nonnegative radii this is equivalent, over a real-closed ordered field,
;; to equality of the circles or existence of exactly one common point.
(defun ht029-circles-tangent-p
    (first-center first-radius second-center second-radius)
  (or
   (equal
    (ht029-distance-squared first-center second-center)
    (ht029-square (ht029-add first-radius second-radius)))
   (equal
    (ht029-distance-squared first-center second-center)
    (ht029-square (ht029-subtract first-radius second-radius)))))

(defun ht029-feuerbach-hypotheses-p
    (a b c mbc mac mab pbc pac pab
       ncenter icenter nradius iradius zero one)
  (and
   (ht029-point-p a)
   (ht029-point-p b)
   (ht029-point-p c)
   (ht029-point-p mbc)
   (ht029-point-p mac)
   (ht029-point-p mab)
   (ht029-point-p pbc)
   (ht029-point-p pac)
   (ht029-point-p pab)
   (ht029-point-p ncenter)
   (ht029-point-p icenter)
   (not (ht029-collinear-p a b c))
   (ht029-midpoint-p a b mab one)
   (ht029-midpoint-p b c mbc one)
   (ht029-midpoint-p c a mac one)
   (ht029-on-circle-p ncenter nradius mbc zero)
   (ht029-on-circle-p ncenter nradius mac zero)
   (ht029-on-circle-p ncenter nradius mab zero)
   (ht029-on-circle-p icenter iradius pbc zero)
   (ht029-on-circle-p icenter iradius pac zero)
   (ht029-on-circle-p icenter iradius pab zero)
   (ht029-collinear-p a b pab)
   (ht029-orthogonal-p a b icenter pab zero)
   (ht029-collinear-p b c pbc)
   (ht029-orthogonal-p b c icenter pbc zero)
   (ht029-collinear-p a c pac)
   (ht029-orthogonal-p a c icenter pac zero)))

(defun-sk hundred-theorems-029-feuerbach-statement (zero one)
  (forall
   (a b c mbc mac mab pbc pac pab
      ncenter icenter nradius iradius)
   (implies
    (and
     (ht029-real-scalar-context-p zero one)
     (ht029-feuerbach-hypotheses-p
      a b c mbc mac mab pbc pac pab
      ncenter icenter nradius iradius zero one))
    (ht029-circles-tangent-p
     ncenter nradius icenter iradius))))

(value-triple :itpeval-statement-checked)
:q
