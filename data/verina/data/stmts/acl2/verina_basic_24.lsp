;; Statement-only formalization of VERINA corpus artifact verina_basic_24,
;; catalog title "firstEvenOddDifference": a deterministic integer-array scan
;; returns the first even entry minus the first odd entry, and its correctness
;; identifies both first-occurrence indices. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements are arbitrary integers.

(defun verina-basic-24-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-24-int-array-p (cdr a)))
    (equal a nil)))

;; These predicates reproduce the source Int remainder tests. With positive
;; divisor two, ACL2 MOD and Lean Int.emod agree on every integer.

(defun verina-basic-24-is-even (n)
  (equal (mod n 2) 0))

(defun verina-basic-24-is-odd (n)
  (not (equal (mod n 2) 0)))

;; The following structural searches are exactly the two bounded membership
;; existentials in the source precondition.

(defun verina-basic-24-contains-even-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (or
       (verina-basic-24-is-even (car a))
       (verina-basic-24-contains-even-p (cdr a)))
    nil))

(defun verina-basic-24-contains-odd-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (or
       (verina-basic-24-is-odd (car a))
       (verina-basic-24-contains-odd-p (cdr a)))
    nil))

(defun verina-basic-24-first-even-odd-difference-precond (a)
  (and
   (< 1 (len a))
   (verina-basic-24-contains-even-p a)
   (verina-basic-24-contains-odd-p a)))

;; Option Nat is represented by :none or the tagged dotted pair
;; (:some . index), keeping none distinct from every natural-number index.

(defun verina-basic-24-option-nat-p (option)
  (or
   (equal option :none)
   (and
    (consp option)
    (equal (car option) :some)
    (natp (cdr option)))))

;; REMAINING is precisely the suffix beginning at source index I. FIRST-EVEN
;; and FIRST-ODD are the source Option Nat loop state. Each recursive call
;; consumes one array entry, records a still-missing index when its parity
;; matches, and returns immediately once both updated options are present.

(defun verina-basic-24-find-first-even-odd-loop
    (a remaining i first-even first-odd)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((x (car remaining))
             (new-first-even
              (if (and
                   (equal first-even :none)
                   (verina-basic-24-is-even x))
                  (cons :some i)
                first-even))
             (new-first-odd
              (if (and
                   (equal first-odd :none)
                   (verina-basic-24-is-odd x))
                  (cons :some i)
                first-odd)))
        (if (and
             (not (equal new-first-even :none))
             (not (equal new-first-odd :none)))
            (- (nth (cdr new-first-even) a)
               (nth (cdr new-first-odd) a))
          (verina-basic-24-find-first-even-odd-loop
           a
           (cdr remaining)
           (+ i 1)
           new-first-even
           new-first-odd)))
    0))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. Starting with the full array, index zero, and two absent options
;; exactly reproduces the source implementation, including its terminal zero
;; branch when the scan reaches the end.

(defun verina-basic-24-first-even-odd-difference (a)
  (verina-basic-24-find-first-even-odd-loop
   a
   a
   0
   :none
   :none))

;; These predicates preserve the source postcondition's universal Nat binders:
;; every index before the chosen even index contains an odd value, and every
;; index before the chosen odd index contains an even value.

(defun-sk verina-basic-24-all-before-odd-p (a i)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k i))
     (verina-basic-24-is-odd (nth k a)))))

(defun-sk verina-basic-24-all-before-even-p (a j)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k j))
     (verina-basic-24-is-even (nth k a)))))

;; This is the source existential postcondition, with the Nat domains of I and
;; J made explicit and the result tied to the entries at those exact indices.

(defun-sk verina-basic-24-postcondition-indices-p (a result)
  (exists (i j)
    (and
     (natp i)
     (natp j)
     (< i (len a))
     (< j (len a))
     (verina-basic-24-is-even (nth i a))
     (verina-basic-24-is-odd (nth j a))
     (equal result
            (- (nth i a)
               (nth j a)))
     (verina-basic-24-all-before-odd-p a i)
     (verina-basic-24-all-before-even-p a j))))

(defun verina-basic-24-first-even-odd-difference-postcond
    (a result)
  (and
   (verina-basic-24-int-array-p a)
   (integerp result)
   (verina-basic-24-postcondition-indices-p
    a
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Array Int input, the complete source precondition, and applies
;; the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-24-first-even-odd-difference-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-24-int-array-p a)
      (verina-basic-24-first-even-odd-difference-precond a))
     (verina-basic-24-first-even-odd-difference-postcond
      a
      (verina-basic-24-first-even-odd-difference a)))))

(value-triple :itpeval-statement-checked)
:q
