;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/queens_bv_Bits_belowqtvc: the 32-bit low-bits mask verification
;; condition relating a complemented left shift to the integer interval
;; containing exactly its set bits. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^32 are in bijection with the source's unsigned
;; 32-bit words. The operations below are reduced modulo 2^32 exactly as in
;; Why3's BV32 bit-vector operations.

(defun queens-bv-below-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun queens-bv-below-u32 (value)
  (mod (ifix value) 4294967296))

(defun queens-bv-below-shift-left (value amount)
  (queens-bv-below-u32
   (ash (queens-bv-below-u32 value)
        (nfix amount))))

(defun queens-bv-below-not (value)
  (queens-bv-below-u32
   (lognot (queens-bv-below-u32 value))))

(defun queens-bv-below-mask (n)
  (queens-bv-below-not
   (queens-bv-below-shift-left
    4294967295
    n)))

(defun queens-bv-below-bit-p (word index)
  (logbitp (nfix index) word))

(defun queens-bv-below-interval-member-p
    (index lower upper)
  (and
   (integerp index)
   (<= lower index)
   (< index upper)))

;; These conservative interfaces represent the source's arbitrary inhabited
;; record type and its bv and mdl projections. The finite-set projection is
;; represented extensionally by membership over every mathematical integer.

(defstub queens-bv-below-raw-t-p (value) t)
(defstub queens-bv-below-bv (self) t)
(defstub queens-bv-below-raw-mdl-member-p
    (self index) t)

(defun queens-bv-below-t-p (value)
  (if (queens-bv-below-raw-t-p value) t nil))

(defun queens-bv-below-mdl-member-p (self index)
  (if (queens-bv-below-raw-mdl-member-p self index)
      t
    nil))

(defun-sk queens-bv-below-t-nonempty-p ()
  (exists (self)
    (queens-bv-below-t-p self)))

(defun-sk queens-bv-below-projection-typing-p ()
  (forall (self)
    (implies
     (queens-bv-below-t-p self)
     (queens-bv-below-bv32-p
      (queens-bv-below-bv self)))))

(defun-sk queens-bv-below-mdl-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (queens-bv-below-mdl-member-p left index)
      (queens-bv-below-mdl-member-p right index)))))

;; This is the source record invariant:
;;   (0 <= i < 32 and bit i of bv self is one) iff i belongs to mdl self.

(defun-sk queens-bv-below-t-invariant-p ()
  (forall (index self)
    (implies
     (and
      (integerp index)
      (queens-bv-below-t-p self))
     (equal
      (and
       (<= 0 index)
       (< index 32)
       (queens-bv-below-bit-p
        (queens-bv-below-bv self)
        index))
      (queens-bv-below-mdl-member-p
       self
       index)))))

;; Source record equality is equality of both projections, and t'inj states
;; that those projections jointly determine a record value.

(defun-sk queens-bv-below-t-injective-p ()
  (forall (left right)
    (implies
     (and
      (queens-bv-below-t-p left)
      (queens-bv-below-t-p right)
      (equal
       (queens-bv-below-bv left)
       (queens-bv-below-bv right))
      (queens-bv-below-mdl-equal-p
       left
       right))
     (equal left right))))

(defun queens-bv-below-source-context-p ()
  (and
   (queens-bv-below-t-nonempty-p)
   (queens-bv-below-projection-typing-p)
   (queens-bv-below-t-invariant-p)
   (queens-bv-below-t-injective-p)))

;; Extensional equality between mdl self and the half-open integer interval
;; [0, upper).

(defun-sk queens-bv-below-mdl-is-interval-p
    (self upper)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (queens-bv-below-mdl-member-p self index)
      (if
       (queens-bv-below-interval-member-p
        index 0 upper)
       t
       nil)))))

;; The constructor invariant for o2 = ~(0xFFFFFFFF << n): its one-bits are
;; exactly the integer indices in [0,n).

(defun-sk queens-bv-below-mask-model-p (n)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (and
       (<= 0 index)
       (< index 32)
       (queens-bv-below-bit-p
        (queens-bv-below-mask n)
        index))
      (if
       (queens-bv-below-interval-member-p
        index 0 n)
       t
       nil)))))

;; Preserve the source universal continuation over every result record. Its
;; premise identifies both projections with o2 and o1; the conclusion repeats
;; the required mdl equality with interval [0,n).

(defun-sk queens-bv-below-all-results-p (n)
  (forall (result)
    (implies
     (queens-bv-below-t-p result)
     (implies
      (and
       (equal
        (queens-bv-below-bv result)
        (queens-bv-below-mask n))
       (queens-bv-below-mdl-is-interval-p
        result
        n))
      (queens-bv-below-mdl-is-interval-p
       result
       n)))))

(defun
    ntp4vc-pearl-queens-bv-bits-belowqtvc-statement
    (n)
  (implies
   (and
    (queens-bv-below-source-context-p)
    (queens-bv-below-bv32-p n)
    (<= n 32))
   (and
    (queens-bv-below-mask-model-p n)
    (queens-bv-below-all-results-p n))))

(value-triple :itpeval-statement-checked)
:q
