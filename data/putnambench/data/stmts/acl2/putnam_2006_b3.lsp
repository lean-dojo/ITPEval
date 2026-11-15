;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_b3:
;; the maximum number of unordered linear partitions of an n-point set in the
;; real plane is choose(n,2)+1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no native completed real field.  The conservative
;; interfaces below present an arbitrary real closed ordered field, with every
;; field, order, closure, and real-closedness law explicit in the statement
;; predicate.  For each fixed n this is a finite first-order ordered-field
;; assertion, so completeness of the theory of real closed fields transfers it
;; bidirectionally between this presentation and the source's real field.
;;
;; A duplicate-free list represents the source finite point set extensionally.
;; A mask represents one subset and its complement.  Since n is positive,
;; requiring the first mask bit to be one selects exactly one representative
;; of each unordered partition.  Both orientations are tested against the
;; source's strict separator inequalities y > m*x+b and y < m*x+b.

(defstub putnam-2006-b3-real-p (x) t)
(defstub putnam-2006-b3-zero () t)
(defstub putnam-2006-b3-one () t)
(defstub putnam-2006-b3-add (x y) t)
(defstub putnam-2006-b3-mul (x y) t)
(defstub putnam-2006-b3-neg (x) t)
(defstub putnam-2006-b3-inv (x) t)
(defstub putnam-2006-b3-lt-op (x y) t)
(defstub putnam-2006-b3-square-root (x) t)
(defstub putnam-2006-b3-odd-root (coefficients) t)

(defun putnam-2006-b3-lt (x y)
  (if (putnam-2006-b3-lt-op x y) t nil))

(defun putnam-2006-b3-real-list-p (values)
  (if (consp values)
      (and
       (putnam-2006-b3-real-p (car values))
       (putnam-2006-b3-real-list-p (cdr values)))
    (equal values nil)))

;; Coefficients are stored in ascending degree order.
(defun putnam-2006-b3-polynomial-eval
    (coefficients x)
  (if (consp coefficients)
      (putnam-2006-b3-add
       (car coefficients)
       (putnam-2006-b3-mul
        x
        (putnam-2006-b3-polynomial-eval
         (cdr coefficients) x)))
    (putnam-2006-b3-zero)))

(defun putnam-2006-b3-odd-degree-polynomial-p
    (coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-2006-b3-real-list-p coefficients)
   (evenp (len coefficients))
   (not
    (equal
     (car (last coefficients))
     (putnam-2006-b3-zero)))))

(defun-sk putnam-2006-b3-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-2006-b3-real-p x)
      (putnam-2006-b3-real-p y)
      (putnam-2006-b3-real-p z))
     (let ((xy-add (putnam-2006-b3-add x y))
           (yz-add (putnam-2006-b3-add y z))
           (xy-mul (putnam-2006-b3-mul x y))
           (yz-mul (putnam-2006-b3-mul y z))
           (neg-x (putnam-2006-b3-neg x))
           (inv-x (putnam-2006-b3-inv x)))
       (and
        (putnam-2006-b3-real-p xy-add)
        (putnam-2006-b3-real-p xy-mul)
        (putnam-2006-b3-real-p neg-x)
        (putnam-2006-b3-real-p inv-x)
        (equal
         (putnam-2006-b3-add xy-add z)
         (putnam-2006-b3-add x yz-add))
        (equal xy-add (putnam-2006-b3-add y x))
        (equal
         (putnam-2006-b3-add x (putnam-2006-b3-zero))
         x)
        (equal
         (putnam-2006-b3-add x neg-x)
         (putnam-2006-b3-zero))
        (equal
         (putnam-2006-b3-mul xy-mul z)
         (putnam-2006-b3-mul x yz-mul))
        (equal xy-mul (putnam-2006-b3-mul y x))
        (equal
         (putnam-2006-b3-mul x (putnam-2006-b3-one))
         x)
        (implies
         (equal x (putnam-2006-b3-zero))
         (equal inv-x (putnam-2006-b3-zero)))
        (implies
         (not (equal x (putnam-2006-b3-zero)))
         (equal
          (putnam-2006-b3-mul x inv-x)
          (putnam-2006-b3-one)))
        (equal
         (putnam-2006-b3-mul x yz-add)
         (putnam-2006-b3-add
          (putnam-2006-b3-mul x y)
          (putnam-2006-b3-mul x z))))))))

(defun-sk putnam-2006-b3-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-2006-b3-real-p x)
      (putnam-2006-b3-real-p y)
      (putnam-2006-b3-real-p z))
     (and
      (not (putnam-2006-b3-lt x x))
      (or
       (equal x y)
       (putnam-2006-b3-lt x y)
       (putnam-2006-b3-lt y x))
      (implies
       (and
        (putnam-2006-b3-lt x y)
        (putnam-2006-b3-lt y z))
       (putnam-2006-b3-lt x z))
      (implies
       (putnam-2006-b3-lt x y)
       (putnam-2006-b3-lt
        (putnam-2006-b3-add x z)
        (putnam-2006-b3-add y z)))
      (implies
       (and
        (putnam-2006-b3-lt (putnam-2006-b3-zero) x)
        (putnam-2006-b3-lt (putnam-2006-b3-zero) y))
       (putnam-2006-b3-lt
        (putnam-2006-b3-zero)
        (putnam-2006-b3-mul x y)))))))

(defun-sk putnam-2006-b3-square-root-laws-p ()
  (forall (x)
    (implies
     (and
      (putnam-2006-b3-real-p x)
      (not
       (putnam-2006-b3-lt
        x
        (putnam-2006-b3-zero))))
     (let ((root (putnam-2006-b3-square-root x)))
       (and
        (putnam-2006-b3-real-p root)
        (equal
         (putnam-2006-b3-mul root root)
         x))))))

(defun-sk putnam-2006-b3-odd-root-laws-p ()
  (forall (coefficients)
    (implies
     (putnam-2006-b3-odd-degree-polynomial-p
      coefficients)
     (let ((root
            (putnam-2006-b3-odd-root coefficients)))
       (and
        (putnam-2006-b3-real-p root)
        (equal
         (putnam-2006-b3-polynomial-eval
          coefficients root)
         (putnam-2006-b3-zero)))))))

(defun putnam-2006-b3-real-closed-field-p ()
  (and
   (putnam-2006-b3-real-p (putnam-2006-b3-zero))
   (putnam-2006-b3-real-p (putnam-2006-b3-one))
   (not
    (equal
     (putnam-2006-b3-zero)
     (putnam-2006-b3-one)))
   (putnam-2006-b3-lt
    (putnam-2006-b3-zero)
    (putnam-2006-b3-one))
   (putnam-2006-b3-field-laws-p)
   (putnam-2006-b3-order-laws-p)
   (putnam-2006-b3-square-root-laws-p)
   (putnam-2006-b3-odd-root-laws-p)))

(defun putnam-2006-b3-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (putnam-2006-b3-real-p (nth 0 point))
   (putnam-2006-b3-real-p (nth 1 point))))

(defun putnam-2006-b3-point-list-p (points)
  (if (consp points)
      (and
       (putnam-2006-b3-point-p (car points))
       (putnam-2006-b3-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-2006-b3-point-finset-p (points n)
  (and
   (true-listp points)
   (putnam-2006-b3-point-list-p points)
   (no-duplicatesp-equal points)
   (equal (len points) n)))

(defun putnam-2006-b3-separated-by-line-p
    (points mask m b)
  (if (consp points)
      (let* ((point (car points))
             (x (nth 0 point))
             (y (nth 1 point))
             (line-height
              (putnam-2006-b3-add
               (putnam-2006-b3-mul m x)
               b)))
        (and
         (if (equal (mod mask 2) 1)
             (putnam-2006-b3-lt line-height y)
           (putnam-2006-b3-lt y line-height))
         (putnam-2006-b3-separated-by-line-p
          (cdr points)
          (floor mask 2)
          m
          b)))
    (equal points nil)))

(defun-sk putnam-2006-b3-separator-exists-p
    (points mask)
  (exists (m b)
    (and
     (putnam-2006-b3-real-p m)
     (putnam-2006-b3-real-p b)
     (putnam-2006-b3-separated-by-line-p
      points mask m b))))

(defun putnam-2006-b3-complement-mask (points mask)
  (- (- (expt 2 (len points)) 1)
     mask))

(defun putnam-2006-b3-linear-partition-p
    (points mask)
  (or
   (putnam-2006-b3-separator-exists-p
    points mask)
   (putnam-2006-b3-separator-exists-p
    points
    (putnam-2006-b3-complement-mask
     points mask))))

(defun putnam-2006-b3-linear-partition-count-through
    (points mask)
  (declare (xargs :measure (nfix mask)))
  (if (zp mask)
      0
    (+
     (if (and
          (equal (mod mask 2) 1)
          (putnam-2006-b3-linear-partition-p
           points mask))
         1
       0)
     (putnam-2006-b3-linear-partition-count-through
      points (- (nfix mask) 1)))))

(defun putnam-2006-b3-linear-partition-count (points)
  (putnam-2006-b3-linear-partition-count-through
   points
   (- (expt 2 (len points)) 1)))

(defun putnam-2006-b3-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+
     (putnam-2006-b3-binomial-coefficient
      (- (nfix n) 1)
      k)
     (putnam-2006-b3-binomial-coefficient
      (- (nfix n) 1)
      (- (nfix k) 1)))))

(defun putnam-2006-b3-solution (n)
  (+ (putnam-2006-b3-binomial-coefficient n 2)
     1))

(defun-sk putnam-2006-b3-attaining-configuration-exists-p (n)
  (exists (witness)
    (and
     (putnam-2006-b3-point-finset-p witness n)
     (equal
      (putnam-2006-b3-linear-partition-count witness)
      (putnam-2006-b3-solution n)))))

;; Existence of an attaining configuration together with the universal upper
;; bound is exactly IsGreatest for the set of linear-partition counts.
(defun putnambench-putnam-2006-b3-statement (n points)
  (implies
   (and
    (putnam-2006-b3-real-closed-field-p)
    (natp n)
    (< 0 n))
   (and
    (putnam-2006-b3-attaining-configuration-exists-p n)
    (implies
     (putnam-2006-b3-point-finset-p points n)
     (<=
      (putnam-2006-b3-linear-partition-count points)
      (putnam-2006-b3-solution n))))))

(value-triple :itpeval-statement-checked)
:q
