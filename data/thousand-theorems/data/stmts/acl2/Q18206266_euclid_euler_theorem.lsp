;; Statement-only formalization of thousand-theorems corpus artifact Q18206266,
;; "Euclid–Euler theorem": every natural number that is even and perfect is
;; 2^k times the prime Mersenne number 2^(k+1)-1 for some natural k. This file
;; contains no proof.

(in-package "ACL2")

(defun q18206266-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (q18206266-no-divisor-from-p n (+ d 1)))
    t))

(defun q18206266-primep (n)
  (and (natp n)
       (< 1 n)
       (q18206266-no-divisor-from-p n 2)))

(defun q18206266-sum-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (and (natp n)
           (natp d))
      (if (zp d)
          0
        (+ (if (equal (mod n d) 0)
               d
             0)
           (q18206266-sum-divisors-through n (- d 1))))
    0))

(defun q18206266-perfectp (n)
  (and (natp n)
       (< 0 n)
       (equal (q18206266-sum-divisors-through n n)
              (* 2 n))))

(defun q18206266-euclid-euler-form-p (n k)
  (and (natp n)
       (natp k)
       (let ((mersenne (- (expt 2 (+ k 1)) 1)))
         (and (q18206266-primep mersenne)
              (equal n
                     (* (expt 2 k) mersenne))))))

(defun-sk q18206266-euclid-euler-witness-exists-p (n)
  (exists (k)
    (q18206266-euclid-euler-form-p n k)))

(defun thousand-theorems-q18206266-euclid-euler-theorem-statement (n)
  (implies
   (and (natp n)
        (equal (mod n 2) 0)
        (q18206266-perfectp n))
   (q18206266-euclid-euler-witness-exists-p n)))

(value-triple :itpeval-statement-checked)
:q
