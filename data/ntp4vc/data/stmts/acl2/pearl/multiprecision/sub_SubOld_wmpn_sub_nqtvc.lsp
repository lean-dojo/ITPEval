;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_SubOld_wmpn_sub_nqtvc: the loop verification
;; condition for equal-length multiprecision subtraction into a separate
;; result pointer, including borrow arithmetic, pointer validity, updates, and
;; frame preservation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented by their canonical unsigned integers.

(defun mpsubout-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpsubout-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpsubout-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpsubout-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones remain arbitrary inhabited source carrier types.
;; Length and the total integer-indexed limb observation are independent
;; selectors, matching the distinct observations made by the source VC.

(defstub mpsubout-pointer-p (pointer) t)
(defstub mpsubout-zone-p (zone) t)
(defstub mpsubout-data-length (pointer) t)
(defstub mpsubout-pelt (pointer index) t)
(defstub mpsubout-offset (pointer) t)
(defstub mpsubout-minimum (pointer) t)
(defstub mpsubout-maximum (pointer) t)
(defstub mpsubout-writable (pointer) t)
(defstub mpsubout-zone (pointer) t)

(defun-sk mpsubout-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpsubout-pointer-p pointer)))

(defun-sk mpsubout-zone-domain-nonempty-p ()
  (exists (zone)
    (mpsubout-zone-p zone)))

(defun-sk mpsubout-interface-typed-p ()
  (forall (pointer)
    (implies
     (mpsubout-pointer-p pointer)
     (and
      (integerp (mpsubout-data-length pointer))
      (<= 0 (mpsubout-data-length pointer))
      (integerp (mpsubout-offset pointer))
      (integerp (mpsubout-minimum pointer))
      (integerp (mpsubout-maximum pointer))
      (booleanp (mpsubout-writable pointer))
      (mpsubout-zone-p
       (mpsubout-zone pointer))))))

(defun-sk mpsubout-limb-observations-typed-p ()
  (forall (pointer index)
    (implies
     (and
      (mpsubout-pointer-p pointer)
      (integerp index))
     (mpsubout-bv64-p
      (mpsubout-pelt pointer index)))))

(defun mpsubout-interface-p ()
  (and
   (mpsubout-pointer-domain-nonempty-p)
   (mpsubout-zone-domain-nonempty-p)
   (mpsubout-interface-typed-p)
   (mpsubout-limb-observations-typed-p)))

;; Int.toNat is used only for source integer exponents and recursion counts.

(defun mpsubout-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

;; Little-endian radix-2^64 value over the total limb observation.

(defun mpsubout-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpsubout-pelt pointer index)
     (*
      18446744073709551616
      (mpsubout-value-from
       pointer
       (+ index 1)
       (- count 1))))))

(defun mpsubout-value (pointer size)
  (mpsubout-value-from
   pointer
   (mpsubout-offset pointer)
   (mpsubout-int-to-nat size)))

(defun mpsubout-radix-power (exponent)
  (expt
   18446744073709551616
   (mpsubout-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsubout-valid-p (pointer size)
  (and
   (mpsubout-pointer-p pointer)
   (mpsubout-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpsubout-minimum pointer))
   (<= (mpsubout-minimum pointer)
       (mpsubout-offset pointer))
   (<= (+ (mpsubout-offset pointer) size)
       (mpsubout-maximum pointer))
   (<= (mpsubout-maximum pointer)
       (mpsubout-data-length pointer))))

(defun mpsubout-copy-fields-p (new old)
  (and
   (equal
    (mpsubout-data-length new)
    (mpsubout-data-length old))
   (equal
    (mpsubout-offset new)
    (mpsubout-offset old))
   (equal
    (mpsubout-minimum new)
    (mpsubout-minimum old))
   (equal
    (mpsubout-maximum new)
    (mpsubout-maximum old))
   (equal
    (mpsubout-writable new)
    (mpsubout-writable old))
   (equal
    (mpsubout-zone new)
    (mpsubout-zone old))))

(defun mpsubout-valid-index-p (pointer index)
  (and
   (<= (mpsubout-minimum pointer)
       (+ (mpsubout-offset pointer) index))
   (< (+ (mpsubout-offset pointer) index)
      (mpsubout-maximum pointer))))

(defun mpsubout-borrow-range-p (borrow)
  (and
   (<= 0 borrow)
   (<= borrow 1)))

;; Equality outside the original result interval.

(defun-sk mpsubout-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpsubout-offset new))
       (<= (+ (mpsubout-offset new) size)
           index))
      (equal
       (mpsubout-pelt new index)
       (mpsubout-pelt old index))))))

;; Extensional equality with the single map update appearing in the source.

(defun-sk mpsubout-single-update-p
    (new old update-index result)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsubout-pelt new index)
      (if (equal index update-index)
          result
        (mpsubout-pelt old index))))))

(defun mpsubout-value-equation-p
    (memory x y size borrow)
  (equal
   (-
    (mpsubout-value memory size)
    (*
     (mpsubout-radix-power size)
     borrow))
   (-
    (mpsubout-value x size)
    (mpsubout-value y size))))

(defun mpsubout-sub-with-borrow-p
    (x y index incoming result borrow)
  (and
   (equal
    (-
     result
     (* 18446744073709551616 borrow))
    (-
     (-
      (mpsubout-pelt
       x
       (+ (mpsubout-offset x) index))
      (mpsubout-pelt
       y
       (+ (mpsubout-offset y) index)))
     incoming))
   (mpsubout-borrow-range-p borrow)))

(defun mpsubout-loop-invariant-p
    (memory original-result x y size index borrow)
  (and
   (<= 0 index)
   (<= index size)
   (mpsubout-value-equation-p
    memory x y index borrow)
   (mpsubout-outside-equal-p
    memory original-result size)
   (mpsubout-borrow-range-p borrow)))

(defun mpsubout-next-invariant-p
    (memory original-result x y size index borrow next-index)
  (and
   (<= 0 (- size index))
   (< (- size next-index)
      (- size index))
   (<= 0 next-index)
   (<= next-index size)
   (mpsubout-value-equation-p
    memory x y next-index borrow)
   (mpsubout-outside-equal-p
    memory original-result size)
   (mpsubout-borrow-range-p borrow)))

(defun-sk mpsubout-all-next-indices-p
    (memory original-result x y size-word index-word borrow)
  (forall (next-index-word)
    (implies
     (mpsubout-bv32-p next-index-word)
     (implies
      (equal
       (mpsubout-signed32 next-index-word)
       (+ (mpsubout-signed32 index-word) 1))
      (mpsubout-next-invariant-p
       memory
       original-result
       x
       y
       (mpsubout-signed32 size-word)
       (mpsubout-signed32 index-word)
       borrow
       (mpsubout-signed32 next-index-word))))))

(defun mpsubout-updated-memory-body-p
    (updated before original-result x y
             size-word index-word result borrow)
  (implies
   (mpsubout-copy-fields-p updated before)
   (implies
    (and
     (mpsubout-single-update-p
      updated
      before
      (+ (mpsubout-offset updated)
         (mpsubout-signed32 index-word))
      result)
     (equal
      (mpsubout-pelt
       updated
       (+ (mpsubout-offset updated)
          (mpsubout-signed32 index-word)))
      result))
    (and
     (mpsubout-int32-in-bounds-p
      (+ (mpsubout-signed32 index-word) 1))
     (mpsubout-all-next-indices-p
      updated
      original-result
      x
      y
      size-word
      index-word
      borrow)))))

(defun-sk mpsubout-all-updated-memories-p
    (before original-result x y
            size-word index-word result borrow)
  (forall (updated)
    (implies
     (mpsubout-pointer-p updated)
     (mpsubout-updated-memory-body-p
      updated
      before
      original-result
      x
      y
      size-word
      index-word
      result
      borrow))))

(defun mpsubout-result-borrow-body-p
    (memory original-result x y
            size-word index-word incoming result borrow)
  (implies
   (mpsubout-sub-with-borrow-p
    x
    y
    (mpsubout-signed32 index-word)
    incoming
    result
    borrow)
   (and
    (and
     (mpsubout-valid-index-p
      memory
      (mpsubout-signed32 index-word))
     (equal (mpsubout-writable memory) t))
    (mpsubout-all-updated-memories-p
     memory
     original-result
     x
     y
     size-word
     index-word
     result
     borrow))))

(defun-sk mpsubout-all-result-borrow-p
    (memory original-result x y size-word index-word incoming)
  (forall (result borrow)
    (implies
     (and
      (mpsubout-bv64-p result)
      (mpsubout-bv64-p borrow))
     (mpsubout-result-borrow-body-p
      memory
      original-result
      x
      y
      size-word
      index-word
      incoming
      result
      borrow))))

(defun mpsubout-loop-branch-p
    (memory original-result x y size-word index-word borrow)
  (if (< (mpsubout-signed32 index-word)
         (mpsubout-signed32 size-word))
      (and
       (mpsubout-valid-index-p
        x
        (mpsubout-signed32 index-word))
       (mpsubout-valid-index-p
        y
        (mpsubout-signed32 index-word))
       (mpsubout-borrow-range-p borrow)
       (mpsubout-all-result-borrow-p
        memory
        original-result
        x
        y
        size-word
        index-word
        borrow))
    (and
     (mpsubout-borrow-range-p borrow)
     (mpsubout-value-equation-p
      memory
      x
      y
      (mpsubout-signed32 size-word)
      borrow)
     (mpsubout-outside-equal-p
      memory
      original-result
      (mpsubout-signed32 size-word)))))

(defun mpsubout-loop-state-body-p
    (original-result x y size-word index-word borrow memory)
  (implies
   (mpsubout-copy-fields-p memory original-result)
   (implies
    (mpsubout-loop-invariant-p
     memory
     original-result
     x
     y
     (mpsubout-signed32 size-word)
     (mpsubout-signed32 index-word)
     borrow)
    (mpsubout-loop-branch-p
     memory
     original-result
     x
     y
     size-word
     index-word
     borrow))))

(defun-sk mpsubout-all-loop-states-p
    (original-result x y size-word)
  (forall (index-word borrow memory)
    (implies
     (and
      (mpsubout-bv32-p index-word)
      (mpsubout-bv64-p borrow)
      (mpsubout-pointer-p memory))
     (mpsubout-loop-state-body-p
      original-result
      x
      y
      size-word
      index-word
      borrow
      memory))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-subold-wmpn-sub-nqtvc-statement
    ()
  (forall (x size-word y result-pointer)
    (implies
     (and
      (mpsubout-interface-p)
      (mpsubout-pointer-p x)
      (mpsubout-bv32-p size-word)
      (mpsubout-pointer-p y)
      (mpsubout-pointer-p result-pointer)
      (mpsubout-valid-p
       x
       (mpsubout-signed32 size-word))
      (mpsubout-valid-p
       y
       (mpsubout-signed32 size-word))
      (mpsubout-valid-p
       result-pointer
       (mpsubout-signed32 size-word))
      (equal (mpsubout-writable result-pointer) t))
     (and
      (<= 0 0)
      (<= 0 (mpsubout-signed32 size-word))
      (mpsubout-value-equation-p
       result-pointer x y 0 0)
      (<= 0 0)
      (<= 0 1)
      (mpsubout-all-loop-states-p
       result-pointer
       x
       y
       size-word)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
