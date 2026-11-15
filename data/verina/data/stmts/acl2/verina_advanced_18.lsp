;; Statement-only formalization of VERINA corpus artifact verina_advanced_18,
;; "isArmstrong": a deterministic decimal-digit computation decides whether a
;; natural number equals the sum of its digits raised to its digit count,
;; together with its Boolean correctness contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True; the Nat input domain is explicit in the
;; final correctness statement.

(defun verina-advanced-18-is-armstrong-precond (n)
  (declare (ignore n))
  t)

;; The fuel is initialized to n. Each recursive source call replaces a
;; positive residual by floor(n / 10), so at most n calls occur and the fuel
;; does not add a cutoff to the source computation.

(defun verina-advanced-18-count-digits-go (n acc fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (natp n))
          (not (natp acc)))
      0
    (if (equal n 0)
        acc
      (if (zp fuel)
          acc
        (verina-advanced-18-count-digits-go
         (floor n 10)
         (+ acc 1)
         (- fuel 1))))))

(defun verina-advanced-18-count-digits (n)
  (if (natp n)
      (verina-advanced-18-count-digits-go
       n
       (if (equal n 0) 1 0)
       n)
    0))

(defun verina-advanced-18-sum-powers-go (n k acc fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (natp n))
          (not (natp k))
          (not (natp acc)))
      0
    (if (equal n 0)
        acc
      (if (zp fuel)
          acc
        (let ((digit (mod n 10)))
          (verina-advanced-18-sum-powers-go
           (floor n 10)
           k
           (+ acc (expt digit k))
           (- fuel 1)))))))

(defun verina-advanced-18-sum-powers (n k)
  (if (and (natp n) (natp k))
      (verina-advanced-18-sum-powers-go n k 0 n)
    0))

(defun verina-advanced-18-is-armstrong (n)
  (let ((k (verina-advanced-18-count-digits n)))
    (equal (verina-advanced-18-sum-powers n k)
           n)))

;; Nat.toString yields one zero digit for 0 and otherwise the ordinary
;; most-significant-first decimal expansion. This separate digit-list
;; computation preserves the source postcondition's string/list fold rather
;; than identifying it definitionally with the implementation loop above.

(defun verina-advanced-18-decimal-digits-positive-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (natp n))
          (zp n)
          (zp fuel))
      nil
    (let ((quotient (floor n 10))
          (digit (mod n 10)))
      (if (equal quotient 0)
          (list digit)
        (append
         (verina-advanced-18-decimal-digits-positive-aux
          quotient
          (- fuel 1))
         (list digit))))))

(defun verina-advanced-18-decimal-digits (n)
  (if (not (natp n))
      nil
    (if (equal n 0)
        (list 0)
      (verina-advanced-18-decimal-digits-positive-aux n n))))

(defun verina-advanced-18-fold-digit-powers (digits k acc)
  (if (consp digits)
      (verina-advanced-18-fold-digit-powers
       (cdr digits)
       k
       (+ acc (expt (car digits) k)))
    acc))

(defun verina-advanced-18-bool-p (result)
  (or (equal result t)
      (equal result nil)))

(defun verina-advanced-18-is-armstrong-postcond (n result)
  (let* ((k (verina-advanced-18-count-digits n))
         (digits (verina-advanced-18-decimal-digits n))
         (decimal-power-sum
          (verina-advanced-18-fold-digit-powers
           digits k 0)))
    (and
     (natp n)
     (verina-advanced-18-bool-p result)
     (implies result
              (equal n decimal-power-sum))
     (implies (not result)
              (not (equal n decimal-power-sum))))))

(defun verina-advanced-18-is-armstrong-spec-satisfied-statement (n)
  (implies
   (and
    (natp n)
    (verina-advanced-18-is-armstrong-precond n))
   (verina-advanced-18-is-armstrong-postcond
    n
    (verina-advanced-18-is-armstrong n))))

(value-triple :itpeval-statement-checked)
:q
