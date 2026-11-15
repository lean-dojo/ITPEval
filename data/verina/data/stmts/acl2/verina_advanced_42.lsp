;; Statement-only formalization of VERINA corpus artifact verina_advanced_42,
;; "maxProfit": the deterministic list program computes the maximum profit
;; from buying before selling, with the complete indexed-list correctness
;; contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-42-nat-listp (prices)
  (declare (xargs :measure (acl2-count prices)))
  (if (consp prices)
      (and
       (natp (car prices))
       (verina-advanced-42-nat-listp (cdr prices)))
    (equal prices nil)))

;; The source precondition is True. The List Nat binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-42-max-profit-precond (prices)
  (declare (ignore prices))
  t)

;; A cons pair represents the source Nat product: its car is the updated
;; minimum price and its cdr is the updated maximum profit. NFIX preserves
;; Lean natural-number subtraction.

(defun verina-advanced-42-update-min-and-profit
    (price min-so-far max-profit)
  (let* ((new-min
          (if (<= min-so-far price)
              min-so-far
            price))
         (profit
          (if (> price min-so-far)
              (nfix (- price min-so-far))
            0))
         (new-max-profit
          (if (>= max-profit profit)
              max-profit
            profit)))
    (cons new-min new-max-profit)))

(defun verina-advanced-42-max-profit-aux
    (prices min-so-far max-profit)
  (declare (xargs :measure (acl2-count prices)))
  (if (consp prices)
      (let ((updated
             (verina-advanced-42-update-min-and-profit
              (car prices)
              min-so-far
              max-profit)))
        (verina-advanced-42-max-profit-aux
         (cdr prices)
         (car updated)
         (cdr updated)))
    max-profit))

;; The proof-valued True precondition argument has no computational effect.
;; This preserves the source empty-list branch and initialization from the
;; first list element.

(defun verina-advanced-42-max-profit (prices)
  (if (consp prices)
      (verina-advanced-42-max-profit-aux
       (cdr prices)
       (car prices)
       0)
    0))

;; Each indexed entry is a cons pair whose car is the price and whose cdr is
;; its zero-based natural index, exactly representing List.zipIdx.

(defun verina-advanced-42-zip-idx-aux (prices index)
  (declare (xargs :measure (acl2-count prices)))
  (if (consp prices)
      (cons
       (cons (car prices) index)
       (verina-advanced-42-zip-idx-aux
        (cdr prices)
        (+ index 1)))
    nil))

(defun verina-advanced-42-zip-idx (prices)
  (verina-advanced-42-zip-idx-aux prices 0))

;; These two predicates reproduce List.Pairwise on the indexed price list.

(defun verina-advanced-42-pairwise-with-first-p
    (first remaining result)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((later (car remaining)))
        (and
         (implies
          (< (cdr first) (cdr later))
          (<= (nfix (- (car later) (car first)))
              result))
         (verina-advanced-42-pairwise-with-first-p
          first
          (cdr remaining)
          result)))
    t))

(defun verina-advanced-42-all-valid-profits-at-most-p
    (indexed-prices result)
  (declare (xargs :measure (acl2-count indexed-prices)))
  (if (consp indexed-prices)
      (and
       (verina-advanced-42-pairwise-with-first-p
        (car indexed-prices)
        (cdr indexed-prices)
        result)
       (verina-advanced-42-all-valid-profits-at-most-p
        (cdr indexed-prices)
        result))
    t))

;; These predicates reproduce the nested List.all test stating that no
;; earlier/later pair has a strictly increasing price.

(defun verina-advanced-42-no-profit-with-first-p
    (first indexed-prices)
  (declare (xargs :measure (acl2-count indexed-prices)))
  (if (consp indexed-prices)
      (let ((second (car indexed-prices)))
        (and
         (or
          (>= (cdr first) (cdr second))
          (<= (car second) (car first)))
         (verina-advanced-42-no-profit-with-first-p
          first
          (cdr indexed-prices))))
    t))

(defun verina-advanced-42-no-profitable-transaction-p
    (remaining indexed-prices)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (verina-advanced-42-no-profit-with-first-p
        (car remaining)
        indexed-prices)
       (verina-advanced-42-no-profitable-transaction-p
        (cdr remaining)
        indexed-prices))
    t))

;; These predicates reproduce the nested List.any test for a transaction
;; attaining a positive result.

(defun verina-advanced-42-achieves-with-first-p
    (first indexed-prices result)
  (declare (xargs :measure (acl2-count indexed-prices)))
  (if (consp indexed-prices)
      (let ((second (car indexed-prices)))
        (or
         (and
          (< (cdr first) (cdr second))
          (equal
           (nfix (- (car second) (car first)))
           result))
         (verina-advanced-42-achieves-with-first-p
          first
          (cdr indexed-prices)
          result)))
    nil))

(defun verina-advanced-42-achieving-transaction-p
    (remaining indexed-prices result)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (or
       (verina-advanced-42-achieves-with-first-p
        (car remaining)
        indexed-prices
        result)
       (verina-advanced-42-achieving-transaction-p
        (cdr remaining)
        indexed-prices
        result))
    nil))

(defun verina-advanced-42-max-profit-postcond
    (prices result)
  (let ((indexed-prices
         (verina-advanced-42-zip-idx prices)))
    (and
     (verina-advanced-42-nat-listp prices)
     (natp result)
     (verina-advanced-42-all-valid-profits-at-most-p
      indexed-prices
      result)
     (iff
      (equal result 0)
      (or
       (<= (len prices) 1)
       (verina-advanced-42-no-profitable-transaction-p
        indexed-prices
        indexed-prices)))
     (implies
      (> result 0)
      (verina-advanced-42-achieving-transaction-p
       indexed-prices
       indexed-prices
       result)))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Nat binder and True precondition; its
;; conclusion applies the complete postcondition to the exact executable
;; result.

(defun verina-advanced-42-max-profit-spec-satisfied-statement
    (prices)
  (implies
   (and
    (verina-advanced-42-nat-listp prices)
    (verina-advanced-42-max-profit-precond prices))
   (verina-advanced-42-max-profit-postcond
    prices
    (verina-advanced-42-max-profit prices))))

(value-triple :itpeval-statement-checked)
:q
