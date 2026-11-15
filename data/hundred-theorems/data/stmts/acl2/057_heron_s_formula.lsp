;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__057, "Heron's Formula": for three arbitrary,
;; possibly degenerate points in the real Euclidean plane, the triangle area
;; is determined by its three side lengths and semiperimeter according to
;; Heron's formula. This file contains no proof.

(in-package "ACL2")

;; The six indeterminates below are the coordinates of generic points A, B,
;; and C. Equality of their canonical integer polynomials is equivalent to
;; equality for every real coordinate assignment.
;;
;; If K is the nonnegative triangle area and a, b, c are the side lengths,
;; Heron's formula is bidirectionally equivalent to
;;
;;   16 K^2 = 2 a^2 b^2 + 2 b^2 c^2 + 2 c^2 a^2
;;              - a^4 - b^4 - c^4.
;;
;; This eliminates only the principal square root. For coordinates, 16 K^2
;; is four times the square of the determinant of B-A and C-A, so the
;; statement has the exact polynomial form encoded below.

;; A polynomial is a sorted list of (monomial . coefficient) pairs. A
;; monomial is a sorted list of variable indices, repeated for powers.

(defun ht057-monomial-multiply (left right)
  (declare (xargs :measure
                  (+ (acl2-count left) (acl2-count right))))
  (cond ((endp left) right)
        ((endp right) left)
        ((<= (car left) (car right))
         (cons (car left)
               (ht057-monomial-multiply (cdr left) right)))
        (t
         (cons (car right)
               (ht057-monomial-multiply left (cdr right))))))

(defun ht057-polynomial-insert
    (monomial coefficient polynomial)
  (cond ((equal coefficient 0) polynomial)
        ((endp polynomial)
         (list (cons monomial coefficient)))
        ((equal monomial (caar polynomial))
         (let ((sum (+ coefficient (cdar polynomial))))
           (if (equal sum 0)
               (cdr polynomial)
             (cons (cons monomial sum) (cdr polynomial)))))
        ((lexorder monomial (caar polynomial))
         (cons (cons monomial coefficient) polynomial))
        (t
         (cons (car polynomial)
               (ht057-polynomial-insert
                monomial coefficient (cdr polynomial))))))

(defun ht057-polynomial-add (left right)
  (if (endp left)
      right
    (ht057-polynomial-add
     (cdr left)
     (ht057-polynomial-insert
      (caar left) (cdar left) right))))

(defun ht057-polynomial-negate (polynomial)
  (if (endp polynomial)
      nil
    (cons (cons (caar polynomial) (- (cdar polynomial)))
          (ht057-polynomial-negate (cdr polynomial)))))

(defun ht057-polynomial-subtract (left right)
  (ht057-polynomial-add
   left
   (ht057-polynomial-negate right)))

(defun ht057-polynomial-multiply-term
    (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (ht057-polynomial-insert
     (ht057-monomial-multiply monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (ht057-polynomial-multiply-term
      monomial coefficient (cdr polynomial)))))

(defun ht057-polynomial-multiply (left right)
  (if (endp left)
      nil
    (ht057-polynomial-add
     (ht057-polynomial-multiply-term
      (caar left) (cdar left) right)
     (ht057-polynomial-multiply (cdr left) right))))

(defun ht057-polynomial-scale (coefficient polynomial)
  (if (or (equal coefficient 0)
          (endp polynomial))
      nil
    (cons (cons (caar polynomial)
                (* coefficient (cdar polynomial)))
          (ht057-polynomial-scale coefficient (cdr polynomial)))))

(defun ht057-polynomial-variable (index)
  (list (cons (list index) 1)))

(defun ht057-generic-point (first-index)
  (list (ht057-polynomial-variable first-index)
        (ht057-polynomial-variable (+ 1 first-index))))

(defun ht057-vector-subtract (left right)
  (if (endp left)
      nil
    (cons (ht057-polynomial-subtract
           (car left) (car right))
          (ht057-vector-subtract
           (cdr left) (cdr right)))))

(defun ht057-inner-product (left right)
  (if (or (endp left) (endp right))
      nil
    (ht057-polynomial-add
     (ht057-polynomial-multiply (car left) (car right))
     (ht057-inner-product (cdr left) (cdr right)))))

(defun ht057-distance-squared (left right)
  (let ((difference (ht057-vector-subtract left right)))
    (ht057-inner-product difference difference)))

(defun ht057-determinant (left right)
  (ht057-polynomial-subtract
   (ht057-polynomial-multiply (car left) (cadr right))
   (ht057-polynomial-multiply (cadr left) (car right))))

(defun hundred-theorems-057-herons-formula-statement ()
  (let* ((point-a (ht057-generic-point 0))
         (point-b (ht057-generic-point 2))
         (point-c (ht057-generic-point 4))
         (a-squared (ht057-distance-squared point-c point-b))
         (b-squared (ht057-distance-squared point-a point-c))
         (c-squared (ht057-distance-squared point-b point-a))
         (determinant
          (ht057-determinant
           (ht057-vector-subtract point-b point-a)
           (ht057-vector-subtract point-c point-a)))
         (sixteen-area-squared
          (ht057-polynomial-scale
           4
           (ht057-polynomial-multiply determinant determinant)))
         (heron-polynomial
          (ht057-polynomial-subtract
           (ht057-polynomial-add
            (ht057-polynomial-scale
             2
             (ht057-polynomial-multiply a-squared b-squared))
            (ht057-polynomial-add
             (ht057-polynomial-scale
              2
              (ht057-polynomial-multiply b-squared c-squared))
             (ht057-polynomial-scale
              2
              (ht057-polynomial-multiply c-squared a-squared))))
           (ht057-polynomial-add
            (ht057-polynomial-multiply a-squared a-squared)
            (ht057-polynomial-add
             (ht057-polynomial-multiply b-squared b-squared)
             (ht057-polynomial-multiply
              c-squared c-squared))))))
    (equal sixteen-area-squared heron-polynomial)))

(value-triple :itpeval-statement-checked)
:q
