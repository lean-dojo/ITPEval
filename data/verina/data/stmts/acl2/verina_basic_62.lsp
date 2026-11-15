;; Statement-only formalization of VERINA corpus artifact verina_basic_62,
;; catalog title "Find": a deterministic linear search of an integer array
;; returns the first index containing the key, or -1 when the key is absent.
;; This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-62-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-62-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int and Int binder domains
;; remain explicit in the final correctness proposition.

(defun verina-basic-62-find-precond (a key)
  (declare (ignore a key))
  t)

;; REMAINING is the suffix beginning at the source recursion index INDEX.
;; Equality returns INDEX immediately; otherwise the exact source computation
;; continues at the next natural index. Exhausting the array returns -1.

(defun verina-basic-62-find-loop (remaining key index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (equal (car remaining) key)
          index
        (verina-basic-62-find-loop
         (cdr remaining)
         key
         (+ index 1)))
    -1))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. Starting at index zero reproduces the executable Lean
;; implementation.

(defun verina-basic-62-find (a key)
  (verina-basic-62-find-loop a key 0))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-62-nth-default-zero (index a)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; These predicates preserve the source postcondition's universal Nat
;; quantifiers and their exact strict bounds.

(defun-sk verina-basic-62-no-key-before-p (a key bound)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i bound))
     (not
      (equal
       (verina-basic-62-nth-default-zero i a)
       key)))))

(defun-sk verina-basic-62-key-absent-p (a key)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a)))
     (not
      (equal
       (verina-basic-62-nth-default-zero i a)
       key)))))

;; This is the complete source postcondition. LEN is Int.ofNat of the array
;; size, NFIX on an integer is Lean's Int.toNat, and the proof-valued
;; precondition argument is unused and erased.

(defun verina-basic-62-find-postcond (a key result)
  (and
   (verina-basic-62-int-array-p a)
   (integerp key)
   (integerp result)
   (or
    (equal result -1)
    (and
     (<= 0 result)
     (< result (len a))))
   (implies
    (not (equal result -1))
    (and
     (equal
      (verina-basic-62-nth-default-zero
       (nfix result)
       a)
      key)
     (verina-basic-62-no-key-before-p
      a
      key
      (nfix result))))
   (implies
    (equal result -1)
    (verina-basic-62-key-absent-p a key))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int and Int domains, assumes exactly the source
;; True precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk verina-basic-62-find-spec-satisfied-statement ()
  (forall (a key)
    (implies
     (and
      (verina-basic-62-int-array-p a)
      (integerp key)
      (verina-basic-62-find-precond a key))
     (verina-basic-62-find-postcond
      a
      key
      (verina-basic-62-find a key)))))

(value-triple :itpeval-statement-checked)
:q
