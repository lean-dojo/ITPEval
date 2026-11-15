;; Statement-only formalization of VERINA corpus artifact verina_basic_39,
;; catalog title "rotateRight": a deterministic program reconstructs an
;; integer list with every entry rotated n positions to the right, preserving
;; its length and indexed values. This file contains no proof.

(in-package "ACL2")

;; Finite Lean List Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-39-integer-listp (values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (integerp (car values))
       (verina-basic-39-integer-listp (cdr values)))
    (equal values nil)))

;; The source precondition is True. The List Int and Nat binder domains remain
;; explicit in the final correctness proposition.

(defun verina-basic-39-rotate-right-precond (l n)
  (declare (ignore l n))
  t)

;; List.headD 0 returns the first integer when present and zero otherwise.

(defun verina-basic-39-head-default-zero (values)
  (if (consp values)
      (car values)
    0))

;; This is the exact List.getD behavior for a natural index, represented
;; independently of ACL2 NTH's out-of-range default.

(defun verina-basic-39-nth-default
    (index values default)
  (if (and
       (natp index)
       (< index (len values)))
      (nth index values)
    default))

;; For positive LEN this is
;; Int.toNat ((Int.ofNat INDEX - Int.ofNat N + Int.ofNat LEN) % LEN).
;; The modulo result is already a natural below LEN. The zero-length fallback
;; is irrelevant to both source uses: the implementation branches before it,
;; and the postcondition calls it only under INDEX < LEN.

(defun verina-basic-39-rotated-index (index n len)
  (if (and
       (natp index)
       (natp n)
       (natp len)
       (< 0 len))
      (mod (+ (- index n) len) len)
    0))

;; INDEX and REMAINING reproduce List.range LEN followed by map. Each emitted
;; entry is exactly the source getD at the corresponding rotated index.

(defun verina-basic-39-rotate-right-build
    (l n len index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (verina-basic-39-nth-default
      (verina-basic-39-rotated-index index n len)
      l
      (verina-basic-39-head-default-zero l))
     (verina-basic-39-rotate-right-build
      l
      n
      len
      (+ index 1)
      (- remaining 1)))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The empty branch returns L unchanged; otherwise this performs
;; exactly the source range-map reconstruction.

(defun verina-basic-39-rotate-right (l n)
  (let ((len (len l)))
    (if (equal len 0)
        l
      (verina-basic-39-rotate-right-build
       l n len 0 len))))

;; Option Int is represented by :none or the tagged dotted pair
;; (:some . value), preserving none distinctly from every integer value.

(defun verina-basic-39-nth-option (index values)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      :none
    (if (consp values)
        (if (zp index)
            (cons :some (car values))
          (verina-basic-39-nth-option
           (- index 1)
           (cdr values)))
      :none)))

;; This preserves the source postcondition's universal Nat index binder and
;; its exact strict bound, including equality of the two List.get? options.

(defun-sk verina-basic-39-rotated-entries-p
    (l n result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len l)))
     (equal
      (verina-basic-39-nth-option i result)
      (verina-basic-39-nth-option
       (verina-basic-39-rotated-index
        i n (len l))
       l)))))

;; This is the complete source postcondition: equal lengths and the pointwise
;; right-rotation equation. The unused proof-valued precondition argument is
;; erased while its Boolean content remains in the final proposition.

(defun verina-basic-39-rotate-right-postcond
    (l n result)
  (and
   (verina-basic-39-integer-listp l)
   (natp n)
   (verina-basic-39-integer-listp result)
   (equal (len result) (len l))
   (verina-basic-39-rotated-entries-p l n result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete List Int and Nat domains, applies the source True
;; precondition, and connects the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-39-rotate-right-spec-satisfied-statement
    ()
  (forall (l n)
    (implies
     (and
      (verina-basic-39-integer-listp l)
      (natp n)
      (verina-basic-39-rotate-right-precond l n))
     (verina-basic-39-rotate-right-postcond
      l
      n
      (verina-basic-39-rotate-right l n)))))

(value-triple :itpeval-statement-checked)
:q
