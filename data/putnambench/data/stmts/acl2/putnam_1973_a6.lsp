;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_a6:
;; seven distinct affine lines over the real numbers cannot have at least six
;; points on exactly three lines and at least four points on exactly two lines.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are presented as an arbitrary real-closed ordered field.  The
;; existence of a seven-line counterexample, with all incidence multiplicities
;; expanded as below, is a first-order sentence in the language of ordered
;; fields.  Real-closed fields are elementarily equivalent, so quantifying over
;; such a presentation is bidirectionally equivalent to the source statement
;; over R; in particular, no restriction to rational coefficients is made.

(defstub putnam-1973-a6-scalar-p (x) t)
(defstub putnam-1973-a6-add (x y) t)
(defstub putnam-1973-a6-mul (x y) t)
(defstub putnam-1973-a6-neg (x) t)
(defstub putnam-1973-a6-inv (x) t)
(defstub putnam-1973-a6-lt (x y) t)

(defun putnam-1973-a6-member-p (x)
  (if (putnam-1973-a6-scalar-p x) t nil))

(defun putnam-1973-a6-sub (x y)
  (putnam-1973-a6-add x (putnam-1973-a6-neg y)))

(defun-sk putnam-1973-a6-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1973-a6-member-p x)
      (putnam-1973-a6-member-p y)
      (putnam-1973-a6-member-p z))
     (and
      (putnam-1973-a6-member-p
       (putnam-1973-a6-add x y))
      (putnam-1973-a6-member-p
       (putnam-1973-a6-mul x y))
      (putnam-1973-a6-member-p
       (putnam-1973-a6-neg x))
      (putnam-1973-a6-member-p
       (putnam-1973-a6-inv x))
      (equal
       (putnam-1973-a6-add
        (putnam-1973-a6-add x y) z)
       (putnam-1973-a6-add
        x (putnam-1973-a6-add y z)))
      (equal
       (putnam-1973-a6-add x y)
       (putnam-1973-a6-add y x))
      (equal
       (putnam-1973-a6-add x 0)
       x)
      (equal
       (putnam-1973-a6-add
        x (putnam-1973-a6-neg x))
       0)
      (equal
       (putnam-1973-a6-mul
        (putnam-1973-a6-mul x y) z)
       (putnam-1973-a6-mul
        x (putnam-1973-a6-mul y z)))
      (equal
       (putnam-1973-a6-mul x y)
       (putnam-1973-a6-mul y x))
      (equal
       (putnam-1973-a6-mul x 1)
       x)
      (implies
       (equal x 0)
       (equal (putnam-1973-a6-inv x) 0))
      (implies
       (not (equal x 0))
       (equal
        (putnam-1973-a6-mul
         x (putnam-1973-a6-inv x))
        1))
      (equal
       (putnam-1973-a6-mul
        x (putnam-1973-a6-add y z))
       (putnam-1973-a6-add
        (putnam-1973-a6-mul x y)
        (putnam-1973-a6-mul x z)))))))

(defun-sk putnam-1973-a6-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1973-a6-member-p x)
      (putnam-1973-a6-member-p y)
      (putnam-1973-a6-member-p z))
     (and
      (not (putnam-1973-a6-lt x x))
      (or
       (equal x y)
       (putnam-1973-a6-lt x y)
       (putnam-1973-a6-lt y x))
      (implies
       (and
        (putnam-1973-a6-lt x y)
        (putnam-1973-a6-lt y z))
       (putnam-1973-a6-lt x z))
      (implies
       (putnam-1973-a6-lt x y)
       (putnam-1973-a6-lt
        (putnam-1973-a6-add x z)
        (putnam-1973-a6-add y z)))
      (implies
       (and
        (putnam-1973-a6-lt 0 x)
        (putnam-1973-a6-lt 0 y))
       (putnam-1973-a6-lt
        0 (putnam-1973-a6-mul x y)))))))

(defun-sk putnam-1973-a6-has-square-root-p (x)
  (exists (root)
    (and
     (putnam-1973-a6-member-p root)
     (equal
      (putnam-1973-a6-mul root root)
      x))))

(defun-sk putnam-1973-a6-square-root-law-p ()
  (forall (x)
    (implies
     (and
      (putnam-1973-a6-member-p x)
      (not (putnam-1973-a6-lt x 0)))
     (putnam-1973-a6-has-square-root-p x))))

(defun putnam-1973-a6-scalar-list-p (values)
  (if (consp values)
      (and
       (putnam-1973-a6-member-p (car values))
       (putnam-1973-a6-scalar-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1973-a6-polynomial-p (coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-1973-a6-scalar-list-p coefficients)
   (not (equal (car (last coefficients)) 0))))

(defun putnam-1973-a6-polynomial-value (coefficients x)
  (if (consp coefficients)
      (putnam-1973-a6-add
       (car coefficients)
       (putnam-1973-a6-mul
        x
        (putnam-1973-a6-polynomial-value
         (cdr coefficients) x)))
    0))

(defun-sk putnam-1973-a6-polynomial-has-root-p
    (coefficients)
  (exists (root)
    (and
     (putnam-1973-a6-member-p root)
     (equal
      (putnam-1973-a6-polynomial-value
       coefficients root)
      0))))

(defun-sk putnam-1973-a6-odd-polynomial-root-law-p ()
  (forall (coefficients)
    (implies
     (and
      (putnam-1973-a6-polynomial-p coefficients)
      (evenp (len coefficients)))
     (putnam-1973-a6-polynomial-has-root-p
      coefficients))))

(defun putnam-1973-a6-real-closed-field-p ()
  (and
   (putnam-1973-a6-member-p 0)
   (putnam-1973-a6-member-p 1)
   (not (equal 0 1))
   (putnam-1973-a6-field-laws-p)
   (putnam-1973-a6-order-laws-p)
   (putnam-1973-a6-lt 0 1)
   (putnam-1973-a6-square-root-law-p)
   (putnam-1973-a6-odd-polynomial-root-law-p)))

;; Each source line y = m*x + b is represented by the list (m b).

(defun putnam-1973-a6-line-p (line)
  (and
   (true-listp line)
   (equal (len line) 2)
   (putnam-1973-a6-member-p (nth 0 line))
   (putnam-1973-a6-member-p (nth 1 line))))

(defun putnam-1973-a6-line-list-p (lines)
  (if (consp lines)
      (and
       (putnam-1973-a6-line-p (car lines))
       (putnam-1973-a6-line-list-p (cdr lines)))
    (equal lines nil)))

;; NIL denotes a parallel pair.  Otherwise the returned pair is their unique
;; affine intersection, computed with the presented field operations.

(defun putnam-1973-a6-line-intersection (first second)
  (let ((first-slope (nth 0 first))
        (first-intercept (nth 1 first))
        (second-slope (nth 0 second))
        (second-intercept (nth 1 second)))
    (if (equal first-slope second-slope)
        nil
      (let ((x
             (putnam-1973-a6-mul
              (putnam-1973-a6-sub
               second-intercept first-intercept)
              (putnam-1973-a6-inv
               (putnam-1973-a6-sub
                first-slope second-slope)))))
        (list
         x
         (putnam-1973-a6-add
          (putnam-1973-a6-mul first-slope x)
          first-intercept))))))

(defun putnam-1973-a6-intersections-with-line
    (line remaining)
  (if (consp remaining)
      (let ((point
             (putnam-1973-a6-line-intersection
              line (car remaining))))
        (if point
            (cons
             point
             (putnam-1973-a6-intersections-with-line
              line (cdr remaining)))
          (putnam-1973-a6-intersections-with-line
           line (cdr remaining))))
    nil))

(defun putnam-1973-a6-pair-intersections (lines)
  (if (consp lines)
      (append
       (putnam-1973-a6-intersections-with-line
        (car lines) (cdr lines))
       (putnam-1973-a6-pair-intersections
        (cdr lines)))
    nil))

(defun putnam-1973-a6-unique-points (points seen)
  (if (consp points)
      (if (member-equal (car points) seen)
          (putnam-1973-a6-unique-points
           (cdr points) seen)
        (putnam-1973-a6-unique-points
         (cdr points) (cons (car points) seen)))
    seen))

(defun putnam-1973-a6-point-on-line-p (point line)
  (equal
   (nth 1 point)
   (putnam-1973-a6-add
    (putnam-1973-a6-mul
     (nth 0 line) (nth 0 point))
    (nth 1 line))))

(defun putnam-1973-a6-point-multiplicity (point lines)
  (if (consp lines)
      (+ (if (putnam-1973-a6-point-on-line-p
              point (car lines))
             1
           0)
         (putnam-1973-a6-point-multiplicity
          point (cdr lines)))
    0))

(defun putnam-1973-a6-count-exact-multiplicity
    (points lines multiplicity)
  (if (consp points)
      (+ (if (equal
              (putnam-1973-a6-point-multiplicity
               (car points) lines)
              multiplicity)
             1
           0)
         (putnam-1973-a6-count-exact-multiplicity
          (cdr points) lines multiplicity))
    0))

(defun putnam-1973-a6-nint (multiplicity lines)
  (putnam-1973-a6-count-exact-multiplicity
   (putnam-1973-a6-unique-points
    (putnam-1973-a6-pair-intersections lines)
    nil)
   lines
   multiplicity))

(defun putnambench-putnam-1973-a6-statement (lines)
  (implies
   (and
    (putnam-1973-a6-real-closed-field-p)
    (true-listp lines)
    (equal (len lines) 7)
    (putnam-1973-a6-line-list-p lines)
    (no-duplicatesp-equal lines))
   (not
    (and
     (<= 6 (putnam-1973-a6-nint 3 lines))
     (<= 4 (putnam-1973-a6-nint 2 lines))))))

(value-triple :itpeval-statement-checked)
:q
