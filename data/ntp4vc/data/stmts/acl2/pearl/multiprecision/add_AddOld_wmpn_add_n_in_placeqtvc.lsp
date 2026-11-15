;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/add_AddOld_wmpn_add_n_in_placeqtvc: the loop
;; verification condition for equal-length in-place multiprecision addition,
;; including carry arithmetic, pointer validity, updates, and framing. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented by their canonical unsigned integers.

(defun mpaddn-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpaddn-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpaddn-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpaddn-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones remain arbitrary inhabited source carrier types.

(defstub mpaddn-pointer-p (pointer) t)
(defstub mpaddn-zone-p (zone) t)
(defstub mpaddn-data-length (pointer) t)
(defstub mpaddn-pelt (pointer index) t)
(defstub mpaddn-offset (pointer) t)
(defstub mpaddn-minimum (pointer) t)
(defstub mpaddn-maximum (pointer) t)
(defstub mpaddn-writable (pointer) t)
(defstub mpaddn-zone (pointer) t)

(defun-sk mpaddn-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpaddn-pointer-p pointer)))

(defun-sk mpaddn-zone-domain-nonempty-p ()
  (exists (zone)
    (mpaddn-zone-p zone)))

(defun-sk mpaddn-interface-typed-p ()
  (forall (pointer index)
    (implies
     (mpaddn-pointer-p pointer)
     (and
      (natp (mpaddn-data-length pointer))
      (integerp (mpaddn-offset pointer))
      (integerp (mpaddn-minimum pointer))
      (integerp (mpaddn-maximum pointer))
      (booleanp (mpaddn-writable pointer))
      (mpaddn-zone-p
       (mpaddn-zone pointer))
      (implies
       (integerp index)
       (mpaddn-bv64-p
        (mpaddn-pelt pointer index)))))))

(defun mpaddn-interface-p ()
  (and
   (mpaddn-pointer-domain-nonempty-p)
   (mpaddn-zone-domain-nonempty-p)
   (mpaddn-interface-typed-p)))

;; Int.toNat is used for source recursion counts and exponents.

(defun mpaddn-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

;; Little-endian radix-2^64 value of the indicated prefix.

(defun mpaddn-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpaddn-pelt pointer index)
     (*
      18446744073709551616
      (mpaddn-value-from
       pointer
       (+ index 1)
       (- count 1))))))

(defun mpaddn-value (pointer size)
  (mpaddn-value-from
   pointer
   (mpaddn-offset pointer)
   (mpaddn-int-to-nat size)))

(defun mpaddn-radix-power (exponent)
  (expt
   18446744073709551616
   (mpaddn-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpaddn-valid-p (pointer size)
  (and
   (mpaddn-pointer-p pointer)
   (mpaddn-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpaddn-minimum pointer))
   (<= (mpaddn-minimum pointer)
       (mpaddn-offset pointer))
   (<= (+ (mpaddn-offset pointer) size)
       (mpaddn-maximum pointer))
   (<= (mpaddn-maximum pointer)
       (mpaddn-data-length pointer))))

(defun mpaddn-copy-fields-p (new old)
  (and
   (equal
    (mpaddn-data-length new)
    (mpaddn-data-length old))
   (equal
    (mpaddn-offset new)
    (mpaddn-offset old))
   (equal
    (mpaddn-minimum new)
    (mpaddn-minimum old))
   (equal
    (mpaddn-maximum new)
    (mpaddn-maximum old))
   (equal
    (mpaddn-writable new)
    (mpaddn-writable old))
   (equal
    (mpaddn-zone new)
    (mpaddn-zone old))))

(defun mpaddn-valid-index-p (pointer index)
  (and
   (<= (mpaddn-minimum pointer)
       (+ (mpaddn-offset pointer) index))
   (< (+ (mpaddn-offset pointer) index)
      (mpaddn-maximum pointer))))

(defun mpaddn-carry-range-p (carry)
  (and
   (<= 0 carry)
   (<= carry 1)))

;; Equality on the source integer-indexed pelts maps.

(defun-sk mpaddn-tail-equal-p
    (new old from size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= from index)
       (< index size))
      (equal
       (mpaddn-pelt
        new
        (+ (mpaddn-offset new) index))
       (mpaddn-pelt
        old
        (+ (mpaddn-offset new) index)))))))

(defun-sk mpaddn-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpaddn-offset new))
       (<= (+ (mpaddn-offset new) size)
           index))
      (equal
       (mpaddn-pelt new index)
       (mpaddn-pelt old index))))))

(defun-sk mpaddn-single-update-p
    (new old update-index result)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpaddn-pelt new index)
      (if (equal index update-index)
          result
        (mpaddn-pelt old index))))))

(defun mpaddn-value-equation-p
    (new old-x y size carry)
  (equal
   (+
    (mpaddn-value new size)
    (*
     (mpaddn-radix-power size)
     carry))
   (+
    (mpaddn-value old-x size)
    (mpaddn-value y size))))

(defun mpaddn-loop-invariant-p
    (memory old-x y size index carry)
  (and
   (<= 0 index)
   (<= index size)
   (mpaddn-value-equation-p
    memory old-x y index carry)
   (mpaddn-carry-range-p carry)
   (mpaddn-tail-equal-p
    memory old-x index size)
   (mpaddn-outside-equal-p
    memory old-x size)))

(defun mpaddn-add-with-carry-p
    (memory y index incoming result carry)
  (and
   (equal
    (+
     result
     (* 18446744073709551616 carry))
    (+
     (mpaddn-pelt
      memory
      (+ (mpaddn-offset memory) index))
     (mpaddn-pelt
      y
      (+ (mpaddn-offset y) index))
     incoming))
   (mpaddn-carry-range-p carry)))

(defun mpaddn-next-invariant-p
    (memory old-x y size index carry next-index)
  (and
   (<= 0 (- size index))
   (< (- size next-index)
      (- size index))
   (<= 0 next-index)
   (<= next-index size)
   (mpaddn-value-equation-p
    memory old-x y next-index carry)
   (mpaddn-carry-range-p carry)
   (mpaddn-tail-equal-p
    memory old-x next-index size)
   (mpaddn-outside-equal-p
    memory old-x size)))

(defun-sk mpaddn-all-next-indices-p
    (memory old-x y size-word index-word carry)
  (forall (next-index-word)
    (implies
     (mpaddn-bv32-p next-index-word)
     (implies
      (equal
       (mpaddn-signed32 next-index-word)
       (+ (mpaddn-signed32 index-word) 1))
      (mpaddn-next-invariant-p
       memory
       old-x
       y
       (mpaddn-signed32 size-word)
       (mpaddn-signed32 index-word)
       carry
       (mpaddn-signed32 next-index-word))))))

(defun mpaddn-updated-memory-body-p
    (updated before old-x y size-word index-word result carry)
  (implies
   (mpaddn-copy-fields-p updated before)
   (implies
    (and
     (mpaddn-single-update-p
      updated
      before
      (+ (mpaddn-offset updated)
         (mpaddn-signed32 index-word))
      result)
     (equal
      (mpaddn-pelt
       updated
       (+ (mpaddn-offset updated)
          (mpaddn-signed32 index-word)))
      result))
    (and
     (mpaddn-int32-in-bounds-p
      (+ (mpaddn-signed32 index-word) 1))
     (mpaddn-all-next-indices-p
      updated
      old-x
      y
      size-word
      index-word
      carry)))))

(defun-sk mpaddn-all-updated-memories-p
    (before old-x y size-word index-word result carry)
  (forall (updated)
    (implies
     (mpaddn-pointer-p updated)
     (mpaddn-updated-memory-body-p
      updated
      before
      old-x
      y
      size-word
      index-word
      result
      carry))))

(defun mpaddn-result-carry-body-p
    (memory old-x y size-word index-word incoming result carry)
  (implies
   (mpaddn-add-with-carry-p
    memory
    y
    (mpaddn-signed32 index-word)
    incoming
    result
    carry)
   (and
    (and
     (mpaddn-valid-index-p
      memory
      (mpaddn-signed32 index-word))
     (equal (mpaddn-writable memory) t))
    (mpaddn-all-updated-memories-p
     memory
     old-x
     y
     size-word
     index-word
     result
     carry))))

(defun-sk mpaddn-all-result-carry-p
    (memory old-x y size-word index-word incoming)
  (forall (result carry)
    (implies
     (and
      (mpaddn-bv64-p result)
      (mpaddn-bv64-p carry))
     (mpaddn-result-carry-body-p
      memory
      old-x
      y
      size-word
      index-word
      incoming
      result
      carry))))

(defun mpaddn-loop-branch-p
    (memory old-x y size-word index-word carry)
  (if (< (mpaddn-signed32 index-word)
         (mpaddn-signed32 size-word))
      (and
       (mpaddn-valid-index-p
        memory
        (mpaddn-signed32 index-word))
       (mpaddn-valid-index-p
        y
        (mpaddn-signed32 index-word))
       (mpaddn-carry-range-p carry)
       (mpaddn-all-result-carry-p
        memory
        old-x
        y
        size-word
        index-word
        carry))
    (and
     (mpaddn-carry-range-p carry)
     (mpaddn-value-equation-p
      memory
      old-x
      y
      (mpaddn-signed32 size-word)
      carry)
     (mpaddn-outside-equal-p
      memory
      old-x
      (mpaddn-signed32 size-word)))))

(defun mpaddn-loop-state-body-p
    (old-x y size-word index-word carry memory)
  (implies
   (mpaddn-copy-fields-p memory old-x)
   (implies
    (mpaddn-loop-invariant-p
     memory
     old-x
     y
     (mpaddn-signed32 size-word)
     (mpaddn-signed32 index-word)
     carry)
    (mpaddn-loop-branch-p
     memory
     old-x
     y
     size-word
     index-word
     carry))))

(defun-sk mpaddn-all-loop-states-p
    (old-x y size-word)
  (forall (index-word carry memory)
    (implies
     (and
      (mpaddn-bv32-p index-word)
      (mpaddn-bv64-p carry)
      (mpaddn-pointer-p memory))
     (mpaddn-loop-state-body-p
      old-x
      y
      size-word
      index-word
      carry
      memory))))

(defun-sk
    ntp4vc-pearl-multiprecision-add-addold-wmpn-add-n-in-placeqtvc-statement
    ()
  (forall (x size-word y)
    (implies
     (and
      (mpaddn-interface-p)
      (mpaddn-pointer-p x)
      (mpaddn-bv32-p size-word)
      (mpaddn-pointer-p y)
      (mpaddn-valid-p
       x
       (mpaddn-signed32 size-word))
      (mpaddn-valid-p
       y
       (mpaddn-signed32 size-word))
      (equal (mpaddn-writable x) t))
     (and
      (<= 0 0)
      (<= 0 (mpaddn-signed32 size-word))
      (equal
       (+
        (mpaddn-value x 0)
        (* (mpaddn-radix-power 0) 0))
       (+
        (mpaddn-value x 0)
        (mpaddn-value y 0)))
      (<= 0 0)
      (<= 0 1)
      (mpaddn-all-loop-states-p
       x
       y
       size-word)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
