;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__023, "Formula for Pythagorean Triples": integer
;; solutions of x^2 + y^2 = z^2 are exactly the scaled Euclidean
;; parametrizations, allowing the legs to be exchanged and either sign for z.
;; Bounded searches from -abs(z) through abs(z) encode the existential integer
;; parameters k, m, and n. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-023-integer-abs (z)
  (if (integerp z)
      (if (< z 0)
          (- z)
        z)
    0))

(defun hundred-theorems-023-pythagorean-triple-p (x y z)
  (and (integerp x)
       (integerp y)
       (integerp z)
       (equal (+ (* x x) (* y y))
              (* z z))))

(defun hundred-theorems-023-parameterized-triple-p
    (x y z k m n)
  (and (integerp x)
       (integerp y)
       (integerp z)
       (integerp k)
       (integerp m)
       (integerp n)
       (or (and (equal x
                       (* k (- (* m m) (* n n))))
                (equal y
                       (* k (* 2 (* m n)))))
           (and (equal x
                       (* k (* 2 (* m n))))
                (equal y
                       (* k (- (* m m) (* n n))))))
       (or (equal z
                  (* k (+ (* m m) (* n n))))
           (equal z
                  (* (- k) (+ (* m m) (* n n)))))))

(defun hundred-theorems-023-witness-n-through-index-p
    (x y z k m bound n-index)
  (declare (xargs :measure (nfix n-index)))
  (if (and (integerp x)
           (integerp y)
           (integerp z)
           (integerp k)
           (integerp m)
           (natp bound)
           (natp n-index))
      (or (hundred-theorems-023-parameterized-triple-p
           x y z k m (- n-index bound))
          (and (not (zp n-index))
               (hundred-theorems-023-witness-n-through-index-p
                x y z k m bound (- n-index 1))))
    nil))

(defun hundred-theorems-023-witness-mn-through-index-p
    (x y z k bound m-index)
  (declare (xargs :measure (nfix m-index)))
  (if (and (integerp x)
           (integerp y)
           (integerp z)
           (integerp k)
           (natp bound)
           (natp m-index))
      (or (hundred-theorems-023-witness-n-through-index-p
           x y z k (- m-index bound) bound (* 2 bound))
          (and (not (zp m-index))
               (hundred-theorems-023-witness-mn-through-index-p
                x y z k bound (- m-index 1))))
    nil))

(defun hundred-theorems-023-witness-kmn-through-index-p
    (x y z bound k-index)
  (declare (xargs :measure (nfix k-index)))
  (if (and (integerp x)
           (integerp y)
           (integerp z)
           (natp bound)
           (natp k-index))
      (or (hundred-theorems-023-witness-mn-through-index-p
           x y z (- k-index bound) bound (* 2 bound))
          (and (not (zp k-index))
               (hundred-theorems-023-witness-kmn-through-index-p
                x y z bound (- k-index 1))))
    nil))

(defun hundred-theorems-023-formula-for-pythagorean-triples-statement
    (x y z)
  (implies
   (and (integerp x)
        (integerp y)
        (integerp z))
   (equal
    (hundred-theorems-023-pythagorean-triple-p x y z)
    (let ((bound (hundred-theorems-023-integer-abs z)))
      (hundred-theorems-023-witness-kmn-through-index-p
       x y z bound (* 2 bound))))))

(value-triple :itpeval-statement-checked)
:q
