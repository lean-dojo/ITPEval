;; Statement-only formalization of Hundred Theorems artifact 094,
;; "The Law of Cosines." For three points A, B, C in a real inner-product
;; plane, the square of BC equals AB^2 + AC^2 - 2 AB AC cos(angle BAC).
;; The scalar structure is arbitrary and all of its laws are explicit
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub ht094-carrier (x) t)
(defstub ht094-add-op (x y) t)
(defstub ht094-multiply-op (x y) t)
(defstub ht094-negate-op (x) t)
(defstub ht094-less-op (x y) t)

(defun ht094-member-p (x)
  (if (ht094-carrier x) t nil))

(defun ht094-add (x y)
  (ht094-add-op x y))

(defun ht094-multiply (x y)
  (ht094-multiply-op x y))

(defun ht094-negate (x)
  (ht094-negate-op x))

(defun ht094-subtract (x y)
  (ht094-add x (ht094-negate y)))

(defun ht094-less (x y)
  (if (ht094-less-op x y) t nil))

(defun ht094-square (x)
  (ht094-multiply x x))

(defun-sk ht094-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht094-member-p x)
      (ht094-member-p y)
      (ht094-member-p z))
     (and
      (ht094-member-p (ht094-add x y))
      (ht094-member-p (ht094-multiply x y))
      (ht094-member-p (ht094-negate x))
      (equal (ht094-add (ht094-add x y) z)
             (ht094-add x (ht094-add y z)))
      (equal (ht094-add x y)
             (ht094-add y x))
      (equal (ht094-add x zero) x)
      (equal (ht094-add x (ht094-negate x)) zero)
      (equal (ht094-multiply (ht094-multiply x y) z)
             (ht094-multiply x (ht094-multiply y z)))
      (equal (ht094-multiply x y)
             (ht094-multiply y x))
      (equal (ht094-multiply x one) x)
      (equal
       (ht094-multiply x (ht094-add y z))
       (ht094-add
        (ht094-multiply x y)
        (ht094-multiply x z)))))))

(defun-sk ht094-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht094-member-p x)
      (ht094-member-p y)
      (ht094-member-p z))
     (and
      (not (ht094-less x x))
      (or
       (equal x y)
       (ht094-less x y)
       (ht094-less y x))
      (implies
       (and
        (ht094-less x y)
        (ht094-less y z))
       (ht094-less x z))
      (implies
       (ht094-less x y)
       (ht094-less
        (ht094-add x z)
        (ht094-add y z)))
      (implies
       (and
        (ht094-less zero x)
        (ht094-less zero y))
       (ht094-less zero (ht094-multiply x y)))))))

(defun ht094-scalar-context-p (zero one)
  (and
   (ht094-member-p zero)
   (ht094-member-p one)
   (not (equal zero one))
   (ht094-less zero one)
   (ht094-ring-laws-p zero one)
   (ht094-order-laws-p zero)))

(defun ht094-point-p (point)
  (and
   (consp point)
   (ht094-member-p (car point))
   (ht094-member-p (cdr point))))

(defun ht094-distance-squared (left right)
  (let ((dx (ht094-subtract (car left) (car right)))
        (dy (ht094-subtract (cdr left) (cdr right))))
    (ht094-add
     (ht094-square dx)
     (ht094-square dy))))

(defun ht094-dot-from (vertex left right)
  (let ((left-x
         (ht094-subtract (car left) (car vertex)))
        (left-y
         (ht094-subtract (cdr left) (cdr vertex)))
        (right-x
         (ht094-subtract (car right) (car vertex)))
        (right-y
         (ht094-subtract (cdr right) (cdr vertex))))
    (ht094-add
     (ht094-multiply left-x right-x)
     (ht094-multiply left-y right-y))))

(defun ht094-nonnegative-p (zero x)
  (and
   (ht094-member-p x)
   (not (ht094-less x zero))))

;; For nonzero adjacent sides the cosine equation uniquely characterizes
;; cos(angle BAC). If either side is zero, both its inner product and the
;; cosine term vanish, matching the degenerate convention used by the source.
(defun ht094-triangle-metric-data-p
    (point-a point-b point-c
     length-ab length-ac length-bc cosine-a
     zero)
  (and
   (ht094-point-p point-a)
   (ht094-point-p point-b)
   (ht094-point-p point-c)
   (ht094-nonnegative-p zero length-ab)
   (ht094-nonnegative-p zero length-ac)
   (ht094-nonnegative-p zero length-bc)
   (ht094-member-p cosine-a)
   (equal
    (ht094-square length-ab)
    (ht094-distance-squared point-a point-b))
   (equal
    (ht094-square length-ac)
    (ht094-distance-squared point-a point-c))
   (equal
    (ht094-square length-bc)
    (ht094-distance-squared point-b point-c))
   (equal
    (ht094-multiply
     (ht094-multiply length-ab length-ac)
     cosine-a)
    (ht094-dot-from point-a point-b point-c))))

(defun ht094-law-of-cosines-conclusion-p
    (length-ab length-ac length-bc cosine-a one)
  (let* ((two (ht094-add one one))
         (cosine-term
          (ht094-multiply
           (ht094-multiply
            (ht094-multiply two length-ab)
            length-ac)
           cosine-a)))
    (equal
     (ht094-square length-bc)
     (ht094-add
      (ht094-add
       (ht094-square length-ab)
       (ht094-square length-ac))
      (ht094-negate cosine-term)))))

(defun-sk hundred-theorems-094-law-of-cosines-statement
    (zero one)
  (forall
   (point-a point-b point-c
    length-ab length-ac length-bc cosine-a)
   (implies
    (and
     (ht094-scalar-context-p zero one)
     (ht094-triangle-metric-data-p
      point-a point-b point-c
      length-ab length-ac length-bc cosine-a
      zero))
    (ht094-law-of-cosines-conclusion-p
     length-ab length-ac length-bc cosine-a one))))

(value-triple :itpeval-statement-checked)
:q
