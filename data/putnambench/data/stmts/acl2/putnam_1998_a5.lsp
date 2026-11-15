;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_a5:
;; a finite cover of an arbitrary real-plane set by open discs has a pairwise
;; disjoint subcollection whose radius-tripled discs still cover the set. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no native complete real type.  These conservative symbols present
;; an arbitrary real closed ordered field, which is elementarily equivalent to
;; the real field for this finite first-order geometric statement.  Every
;; field, order, closure, and real-closedness law used by the encoding is an
;; explicit hypothesis of the statement predicate.

(defstub putnam-1998-a5-real-p (x) t)
(defstub putnam-1998-a5-zero () t)
(defstub putnam-1998-a5-one () t)
(defstub putnam-1998-a5-add (x y) t)
(defstub putnam-1998-a5-mul (x y) t)
(defstub putnam-1998-a5-neg (x) t)
(defstub putnam-1998-a5-inv (x) t)
(defstub putnam-1998-a5-lt-op (x y) t)
(defstub putnam-1998-a5-sqrt (x) t)
(defstub putnam-1998-a5-odd-root (coefficients) t)

;; This generic predicate is the source's arbitrary set E subseteq R^2.  It is
;; not replaced by a finite list or sampled collection of points.
(defstub putnam-1998-a5-e-member-p (x y) t)

(defun putnam-1998-a5-lt (x y)
  (if (putnam-1998-a5-lt-op x y) t nil))

(defun putnam-1998-a5-sub (x y)
  (putnam-1998-a5-add x (putnam-1998-a5-neg y)))

(defun putnam-1998-a5-square (x)
  (putnam-1998-a5-mul x x))

(defun putnam-1998-a5-three ()
  (putnam-1998-a5-add
   (putnam-1998-a5-one)
   (putnam-1998-a5-add
    (putnam-1998-a5-one)
    (putnam-1998-a5-one))))

(defun-sk putnam-1998-a5-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1998-a5-real-p x)
      (putnam-1998-a5-real-p y)
      (putnam-1998-a5-real-p z))
     (and
      (putnam-1998-a5-real-p
       (putnam-1998-a5-add x y))
      (putnam-1998-a5-real-p
       (putnam-1998-a5-mul x y))
      (putnam-1998-a5-real-p
       (putnam-1998-a5-neg x))
      (putnam-1998-a5-real-p
       (putnam-1998-a5-inv x))
      (equal
       (putnam-1998-a5-add
        (putnam-1998-a5-add x y)
        z)
       (putnam-1998-a5-add
        x
        (putnam-1998-a5-add y z)))
      (equal
       (putnam-1998-a5-add x y)
       (putnam-1998-a5-add y x))
      (equal
       (putnam-1998-a5-add x (putnam-1998-a5-zero))
       x)
      (equal
       (putnam-1998-a5-add x (putnam-1998-a5-neg x))
       (putnam-1998-a5-zero))
      (equal
       (putnam-1998-a5-mul
        (putnam-1998-a5-mul x y)
        z)
       (putnam-1998-a5-mul
        x
        (putnam-1998-a5-mul y z)))
      (equal
       (putnam-1998-a5-mul x y)
       (putnam-1998-a5-mul y x))
      (equal
       (putnam-1998-a5-mul x (putnam-1998-a5-one))
       x)
      (implies
       (equal x (putnam-1998-a5-zero))
       (equal
        (putnam-1998-a5-inv x)
        (putnam-1998-a5-zero)))
      (implies
       (not (equal x (putnam-1998-a5-zero)))
       (equal
        (putnam-1998-a5-mul x (putnam-1998-a5-inv x))
        (putnam-1998-a5-one)))
      (equal
       (putnam-1998-a5-mul
        x
        (putnam-1998-a5-add y z))
       (putnam-1998-a5-add
        (putnam-1998-a5-mul x y)
        (putnam-1998-a5-mul x z)))))))

(defun-sk putnam-1998-a5-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1998-a5-real-p x)
      (putnam-1998-a5-real-p y)
      (putnam-1998-a5-real-p z))
     (and
      (not (putnam-1998-a5-lt x x))
      (or
       (equal x y)
       (putnam-1998-a5-lt x y)
       (putnam-1998-a5-lt y x))
      (implies
       (and
        (putnam-1998-a5-lt x y)
        (putnam-1998-a5-lt y z))
       (putnam-1998-a5-lt x z))
      (implies
       (putnam-1998-a5-lt x y)
       (putnam-1998-a5-lt
        (putnam-1998-a5-add x z)
        (putnam-1998-a5-add y z)))
      (implies
       (and
        (putnam-1998-a5-lt (putnam-1998-a5-zero) x)
        (putnam-1998-a5-lt (putnam-1998-a5-zero) y))
       (putnam-1998-a5-lt
        (putnam-1998-a5-zero)
        (putnam-1998-a5-mul x y)))))))

(defun putnam-1998-a5-real-list-p (values)
  (if (consp values)
      (and
       (putnam-1998-a5-real-p (car values))
       (putnam-1998-a5-real-list-p (cdr values)))
    (equal values nil)))

;; Coefficients are stored in ascending degree order.
(defun putnam-1998-a5-polynomial-eval
    (coefficients x)
  (if (consp coefficients)
      (putnam-1998-a5-add
       (car coefficients)
       (putnam-1998-a5-mul
        x
        (putnam-1998-a5-polynomial-eval
         (cdr coefficients) x)))
    (putnam-1998-a5-zero)))

(defun putnam-1998-a5-odd-degree-polynomial-p
    (coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-1998-a5-real-list-p coefficients)
   (evenp (len coefficients))
   (not
    (equal
     (car (last coefficients))
     (putnam-1998-a5-zero)))))

(defun-sk putnam-1998-a5-square-root-laws-p ()
  (forall (x)
    (implies
     (and
      (putnam-1998-a5-real-p x)
      (not
       (putnam-1998-a5-lt
        x
        (putnam-1998-a5-zero))))
     (and
      (putnam-1998-a5-real-p
       (putnam-1998-a5-sqrt x))
      (equal
       (putnam-1998-a5-square
        (putnam-1998-a5-sqrt x))
       x)))))

(defun-sk putnam-1998-a5-odd-root-laws-p ()
  (forall (coefficients)
    (implies
     (putnam-1998-a5-odd-degree-polynomial-p
      coefficients)
     (and
      (putnam-1998-a5-real-p
       (putnam-1998-a5-odd-root coefficients))
      (equal
       (putnam-1998-a5-polynomial-eval
        coefficients
        (putnam-1998-a5-odd-root coefficients))
       (putnam-1998-a5-zero))))))

(defun putnam-1998-a5-real-closed-field-p ()
  (and
   (putnam-1998-a5-real-p
    (putnam-1998-a5-zero))
   (putnam-1998-a5-real-p
    (putnam-1998-a5-one))
   (not
    (equal
     (putnam-1998-a5-zero)
     (putnam-1998-a5-one)))
   (putnam-1998-a5-lt
    (putnam-1998-a5-zero)
    (putnam-1998-a5-one))
   (putnam-1998-a5-field-laws-p)
   (putnam-1998-a5-order-laws-p)
   (putnam-1998-a5-square-root-laws-p)
   (putnam-1998-a5-odd-root-laws-p)))

;; A disc is the three-element list (center-x center-y radius).

(defun putnam-1998-a5-disc-x (disc)
  (nth 0 disc))

(defun putnam-1998-a5-disc-y (disc)
  (nth 1 disc))

(defun putnam-1998-a5-disc-radius (disc)
  (nth 2 disc))

(defun putnam-1998-a5-disc-p (disc)
  (and
   (true-listp disc)
   (equal (len disc) 3)
   (putnam-1998-a5-real-p
    (putnam-1998-a5-disc-x disc))
   (putnam-1998-a5-real-p
    (putnam-1998-a5-disc-y disc))
   (putnam-1998-a5-real-p
    (putnam-1998-a5-disc-radius disc))
   (putnam-1998-a5-lt
    (putnam-1998-a5-zero)
    (putnam-1998-a5-disc-radius disc))))

(defun putnam-1998-a5-disc-list-p (discs)
  (if (consp discs)
      (and
       (putnam-1998-a5-disc-p (car discs))
       (putnam-1998-a5-disc-list-p (cdr discs)))
    (equal discs nil)))

(defun putnam-1998-a5-point-in-scaled-ball-p
    (x y disc scale)
  (let ((dx
         (putnam-1998-a5-sub
          x
          (putnam-1998-a5-disc-x disc)))
        (dy
         (putnam-1998-a5-sub
          y
          (putnam-1998-a5-disc-y disc)))
        (scaled-radius
         (putnam-1998-a5-mul
          scale
          (putnam-1998-a5-disc-radius disc))))
    (putnam-1998-a5-lt
     (putnam-1998-a5-add
      (putnam-1998-a5-square dx)
      (putnam-1998-a5-square dy))
     (putnam-1998-a5-square scaled-radius))))

(defun putnam-1998-a5-point-in-some-ball-p
    (x y discs)
  (if (consp discs)
      (or
       (putnam-1998-a5-point-in-scaled-ball-p
        x y (car discs) (putnam-1998-a5-one))
       (putnam-1998-a5-point-in-some-ball-p
        x y (cdr discs)))
    nil))

(defun-sk putnam-1998-a5-source-cover-p (discs)
  (forall (x y)
    (implies
     (and
      (putnam-1998-a5-real-p x)
      (putnam-1998-a5-real-p y)
      (putnam-1998-a5-e-member-p x y))
     (putnam-1998-a5-point-in-some-ball-p
      x y discs))))

(defun-sk putnam-1998-a5-balls-disjoint-p
    (left right)
  (forall (x y)
    (implies
     (and
      (putnam-1998-a5-real-p x)
      (putnam-1998-a5-real-p y))
     (not
      (and
       (putnam-1998-a5-point-in-scaled-ball-p
        x y left (putnam-1998-a5-one))
       (putnam-1998-a5-point-in-scaled-ball-p
        x y right (putnam-1998-a5-one)))))))

(defun putnam-1998-a5-index-list-p
    (indices disc-count)
  (if (consp indices)
      (and
       (natp (car indices))
       (< (car indices) disc-count)
       (putnam-1998-a5-index-list-p
        (cdr indices) disc-count))
    (equal indices nil)))

(defun putnam-1998-a5-disjoint-from-indices-p
    (index indices discs)
  (if (consp indices)
      (and
       (putnam-1998-a5-balls-disjoint-p
        (nth index discs)
        (nth (car indices) discs))
       (putnam-1998-a5-disjoint-from-indices-p
        index (cdr indices) discs))
    t))

(defun putnam-1998-a5-pairwise-disjoint-p
    (indices discs)
  (if (consp indices)
      (and
       (putnam-1998-a5-disjoint-from-indices-p
        (car indices) (cdr indices) discs)
       (putnam-1998-a5-pairwise-disjoint-p
        (cdr indices) discs))
    t))

(defun putnam-1998-a5-point-in-selected-triple-p
    (x y indices discs)
  (if (consp indices)
      (or
       (putnam-1998-a5-point-in-scaled-ball-p
        x
        y
        (nth (car indices) discs)
        (putnam-1998-a5-three))
       (putnam-1998-a5-point-in-selected-triple-p
        x y (cdr indices) discs))
    nil))

(defun-sk putnam-1998-a5-target-cover-p
    (indices discs)
  (forall (x y)
    (implies
     (and
      (putnam-1998-a5-real-p x)
      (putnam-1998-a5-real-p y)
      (putnam-1998-a5-e-member-p x y))
     (putnam-1998-a5-point-in-selected-triple-p
      x y indices discs))))

(defun putnam-1998-a5-selection-p
    (indices discs)
  (and
   (putnam-1998-a5-index-list-p
    indices (len discs))
   (<= (len indices) (len discs))
   (putnam-1998-a5-pairwise-disjoint-p
    indices discs)
   (putnam-1998-a5-target-cover-p
    indices discs)))

;; The subcollection is an internal existential witness, exactly as in the
;; source theorem; no particular selection algorithm is asserted.
(defun-sk putnam-1998-a5-selection-exists-p
    (discs)
  (exists (indices)
    (putnam-1998-a5-selection-p indices discs)))

(defun putnambench-putnam-1998-a5-statement
    (discs)
  (implies
   (and
    (putnam-1998-a5-real-closed-field-p)
    (putnam-1998-a5-disc-list-p discs)
    (putnam-1998-a5-source-cover-p discs))
   (putnam-1998-a5-selection-exists-p discs)))

(value-triple :itpeval-statement-checked)
:q
