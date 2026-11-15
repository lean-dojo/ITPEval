;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__070, "The Perfect Number Theorem": a natural
;; number is even and perfect exactly when it is 2^k times the prime Mersenne
;; number 2^(k+1)-1 for some natural k. The bounded search through n encodes
;; this existential witness. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-070-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (hundred-theorems-070-no-divisor-from-p n (+ d 1)))
    t))

(defun hundred-theorems-070-primep (n)
  (and (natp n)
       (< 1 n)
       (hundred-theorems-070-no-divisor-from-p n 2)))

(defun hundred-theorems-070-sum-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (and (natp n)
           (natp d))
      (if (zp d)
          0
        (+ (if (equal (mod n d) 0)
               d
             0)
           (hundred-theorems-070-sum-divisors-through
            n (- d 1))))
    0))

(defun hundred-theorems-070-perfectp (n)
  (and (natp n)
       (< 0 n)
       (equal
        (hundred-theorems-070-sum-divisors-through n n)
        (* 2 n))))

(defun hundred-theorems-070-euclid-euler-form-p (n k)
  (and (natp n)
       (natp k)
       (let ((mersenne (- (expt 2 (+ k 1)) 1)))
         (and (hundred-theorems-070-primep mersenne)
              (equal n
                     (* (expt 2 k) mersenne))))))

(defun hundred-theorems-070-witness-through-k-p (n k)
  (declare (xargs :measure (nfix k)))
  (if (and (natp n)
           (natp k))
      (or (hundred-theorems-070-euclid-euler-form-p n k)
          (and (not (zp k))
               (hundred-theorems-070-witness-through-k-p
                n (- k 1))))
    nil))

(defun hundred-theorems-070-perfect-number-theorem-statement (n)
  (implies
   (natp n)
   (equal
    (and (equal (mod n 2) 0)
         (hundred-theorems-070-perfectp n))
    (hundred-theorems-070-witness-through-k-p n n))))

(value-triple :itpeval-statement-checked)
:q
