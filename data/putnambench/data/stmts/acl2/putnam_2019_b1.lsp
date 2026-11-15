;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_b1:
;; the number of four-point subsets of the specified lattice-point set P_n
;; that are vertices of a square is 5*n + 1. This file contains no proof.

(in-package "ACL2")

;; If x^2+y^2 = 2^k with k <= n, then |x| and |y| are at most 2^n.
;; Thus enumerating the integer box [-2^n,2^n]^2 and filtering by the source
;; predicate constructs exactly P_n, rather than a bounded approximation.

(defun putnam-2019-b1-square (x)
  (* x x))

(defun putnam-2019-b1-squared-distance (left right)
  (+ (putnam-2019-b1-square
      (- (car left) (car right)))
     (putnam-2019-b1-square
      (- (cdr left) (cdr right)))))

(defun putnam-2019-b1-power-of-two-through-p (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (and (natp value)
           (natp exponent))
      (or (equal value (expt 2 exponent))
          (and (not (zp exponent))
               (putnam-2019-b1-power-of-two-through-p
                value (- exponent 1))))
    nil))

(defun putnam-2019-b1-point-in-pn-p (x y n)
  (and
   (integerp x)
   (integerp y)
   (natp n)
   (or
    (and (equal x 0)
         (equal y 0))
    (putnam-2019-b1-power-of-two-through-p
     (+ (putnam-2019-b1-square x)
        (putnam-2019-b1-square y))
     n))))

(defun putnam-2019-b1-pn-row
    (n x remaining bound)
  (declare (xargs :measure (nfix remaining)))
  (if (and (natp n)
           (integerp x)
           (natp remaining)
           (natp bound))
      (let ((y (- remaining bound)))
        (if (zp remaining)
            (if (putnam-2019-b1-point-in-pn-p x y n)
                (list (cons x y))
              nil)
          (if (putnam-2019-b1-point-in-pn-p x y n)
              (cons
               (cons x y)
               (putnam-2019-b1-pn-row
                n x (- remaining 1) bound))
            (putnam-2019-b1-pn-row
             n x (- remaining 1) bound))))
    nil))

(defun putnam-2019-b1-pn-box
    (n remaining bound)
  (declare (xargs :measure (nfix remaining)))
  (if (and (natp n)
           (natp remaining)
           (natp bound))
      (let* ((x (- remaining bound))
             (row
              (putnam-2019-b1-pn-row
               n x (* 2 bound) bound)))
        (if (zp remaining)
            row
          (append
           row
           (putnam-2019-b1-pn-box
            n (- remaining 1) bound))))
    nil))

(defun putnam-2019-b1-pn (n)
  (if (natp n)
      (let ((bound (expt 2 n)))
        (putnam-2019-b1-pn-box
         n (* 2 bound) bound))
    nil))

;; Equality of Euclidean distances is equivalent to equality of their
;; nonnegative squares. For four distinct points, the three calls below are
;; exactly the three cyclic orderings up to rotation and reversal, so this
;; unfolds the source condition of four equal sides and equal diagonals.

(defun putnam-2019-b1-square-cycle-p (a b c d)
  (let ((side
         (putnam-2019-b1-squared-distance a b)))
    (and
     (< 0 side)
     (equal
      (putnam-2019-b1-squared-distance b c)
      side)
     (equal
      (putnam-2019-b1-squared-distance c d)
      side)
     (equal
      (putnam-2019-b1-squared-distance d a)
      side)
     (equal
      (putnam-2019-b1-squared-distance a c)
      (putnam-2019-b1-squared-distance b d)))))

(defun putnam-2019-b1-square-set-p (a b c d)
  (or
   (putnam-2019-b1-square-cycle-p a b c d)
   (putnam-2019-b1-square-cycle-p a b d c)
   (putnam-2019-b1-square-cycle-p a c b d)))

;; P_n contains no duplicate points. These four nested tail traversals choose
;; indices i<j<k<l, hence count every four-point subset exactly once.

(defun putnam-2019-b1-count-fourth (a b c points)
  (if (endp points)
      0
    (+ (if (putnam-2019-b1-square-set-p
            a b c (car points))
           1
         0)
       (putnam-2019-b1-count-fourth
        a b c (cdr points)))))

(defun putnam-2019-b1-count-third (a b points)
  (if (endp points)
      0
    (+ (putnam-2019-b1-count-fourth
        a b (car points) (cdr points))
       (putnam-2019-b1-count-third
        a b (cdr points)))))

(defun putnam-2019-b1-count-second (a points)
  (if (endp points)
      0
    (+ (putnam-2019-b1-count-third
        a (car points) (cdr points))
       (putnam-2019-b1-count-second
        a (cdr points)))))

(defun putnam-2019-b1-square-count (points)
  (if (endp points)
      0
    (+ (putnam-2019-b1-count-second
        (car points) (cdr points))
       (putnam-2019-b1-square-count
        (cdr points)))))

(defun putnambench-putnam-2019-b1-statement (n)
  (implies
   (natp n)
   (equal
    (putnam-2019-b1-square-count
     (putnam-2019-b1-pn n))
    (+ (* 5 n) 1))))

(value-triple :itpeval-statement-checked)
:q
