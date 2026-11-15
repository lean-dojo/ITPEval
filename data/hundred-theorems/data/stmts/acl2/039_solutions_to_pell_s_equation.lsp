;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__039, "Solutions to Pell's Equation": for every
;; nonsquare natural parameter D, there are natural x0 and y0 giving the least
;; nontrivial positive solution of x^2 - D*y^2 = 1, and every integer solution
;; is obtained, up to independent signs, by a natural power of (x0,y0).
;; This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-039-integer-abs (z)
  (if (integerp z)
      (if (< z 0)
          (- z)
        z)
    0))

(defun hundred-theorems-039-square-witness-through-p (n k)
  (declare (xargs :measure (nfix k)))
  (if (and (natp n)
           (natp k))
      (or (equal (* k k) n)
          (and (not (zp k))
               (hundred-theorems-039-square-witness-through-p
                n (- k 1))))
    nil))

(defun hundred-theorems-039-perfect-square-p (n)
  (and (natp n)
       (hundred-theorems-039-square-witness-through-p n n)))

(defun hundred-theorems-039-no-smaller-positive-solution-through-y-p
    (D y)
  (declare (xargs :measure (nfix y)))
  (if (and (natp D)
           (natp y))
      (if (zp y)
          t
        (and
         (not
          (hundred-theorems-039-perfect-square-p
           (+ 1 (* D (* y y)))))
         (hundred-theorems-039-no-smaller-positive-solution-through-y-p
          D (- y 1))))
    nil))

(defun hundred-theorems-039-fundamental-solution-p (D x0 y0)
  (and (natp D)
       (not (hundred-theorems-039-perfect-square-p D))
       (natp x0)
       (natp y0)
       (< 0 y0)
       (equal (* x0 x0)
              (+ 1 (* D (* y0 y0))))
       (hundred-theorems-039-no-smaller-positive-solution-through-y-p
        D (- y0 1))))

(defun hundred-theorems-039-pell-power-pair (D x0 y0 n)
  (declare (xargs :measure (nfix n)))
  (if (and (natp D)
           (natp x0)
           (natp y0)
           (natp n))
      (if (zp n)
          (cons 1 0)
        (let* ((previous
                (hundred-theorems-039-pell-power-pair
                 D x0 y0 (- n 1)))
               (previous-x (car previous))
               (previous-y (cdr previous)))
          (cons
           (+ (* x0 previous-x)
              (* D (* y0 previous-y)))
           (+ (* y0 previous-x)
              (* x0 previous-y)))))
    (cons 0 0)))

(defun hundred-theorems-039-power-matches-p
    (D x0 y0 x y n)
  (if (and (natp D)
           (natp x0)
           (natp y0)
           (natp x)
           (natp y)
           (natp n))
      (let ((power
             (hundred-theorems-039-pell-power-pair D x0 y0 n)))
        (and (equal x (car power))
             (equal y (cdr power))))
    nil))

(defun hundred-theorems-039-power-matches-through-p
    (D x0 y0 x y n)
  (declare (xargs :measure (nfix n)))
  (if (and (natp D)
           (natp x0)
           (natp y0)
           (natp x)
           (natp y)
           (natp n))
      (or (hundred-theorems-039-power-matches-p
           D x0 y0 x y n)
          (and (not (zp n))
               (hundred-theorems-039-power-matches-through-p
                D x0 y0 x y (- n 1))))
    nil))

(defun hundred-theorems-039-pell-solution-p (D x y)
  (and (natp D)
       (integerp x)
       (integerp y)
       (equal (- (* x x)
                 (* D (* y y)))
              1)))

;; Powers of a positive fundamental solution have y-coordinate at least
;; their exponent, so abs(y) is a complete finite bound for this test.
(defun-sk hundred-theorems-039-generator-classifies-p
    (D x0 y0)
  (forall (x y)
    (implies
     (and (integerp x)
          (integerp y))
     (let ((absolute-x
            (hundred-theorems-039-integer-abs x))
           (absolute-y
            (hundred-theorems-039-integer-abs y)))
       (equal
        (hundred-theorems-039-pell-solution-p D x y)
        (hundred-theorems-039-power-matches-through-p
         D x0 y0 absolute-x absolute-y absolute-y))))))

(defun-sk hundred-theorems-039-solutions-to-pell-equation-statement
    (D)
  (exists (x0 y0)
    (implies
     (and
      (natp D)
      (not (hundred-theorems-039-perfect-square-p D)))
     (and
      (hundred-theorems-039-fundamental-solution-p D x0 y0)
      (hundred-theorems-039-generator-classifies-p D x0 y0)))))

(value-triple :itpeval-statement-checked)
:q
