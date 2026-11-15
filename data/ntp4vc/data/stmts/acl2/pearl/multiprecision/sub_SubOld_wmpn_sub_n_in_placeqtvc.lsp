;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_SubOld_wmpn_sub_n_in_placeqtvc: the loop
;; verification condition for equal-length in-place multiprecision
;; subtraction, including borrow arithmetic, pointer validity, updates, and
;; framing. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented by their canonical unsigned integers.

(defun mpsubn-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpsubn-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpsubn-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpsubn-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones remain arbitrary inhabited source carrier types.
;; Length and the total integer-indexed limb observation are independent
;; selectors, matching the distinct observations made by the source VC.

(defstub mpsubn-pointer-p (pointer) t)
(defstub mpsubn-zone-p (zone) t)
(defstub mpsubn-data-length (pointer) t)
(defstub mpsubn-pelt (pointer index) t)
(defstub mpsubn-offset (pointer) t)
(defstub mpsubn-minimum (pointer) t)
(defstub mpsubn-maximum (pointer) t)
(defstub mpsubn-writable (pointer) t)
(defstub mpsubn-zone (pointer) t)

(defun-sk mpsubn-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpsubn-pointer-p pointer)))

(defun-sk mpsubn-zone-domain-nonempty-p ()
  (exists (zone)
    (mpsubn-zone-p zone)))

(defun-sk mpsubn-interface-typed-p ()
  (forall (pointer)
    (implies
     (mpsubn-pointer-p pointer)
     (and
      (integerp (mpsubn-data-length pointer))
      (<= 0 (mpsubn-data-length pointer))
      (integerp (mpsubn-offset pointer))
      (integerp (mpsubn-minimum pointer))
      (integerp (mpsubn-maximum pointer))
      (booleanp (mpsubn-writable pointer))
      (mpsubn-zone-p
       (mpsubn-zone pointer))))))

(defun-sk mpsubn-limb-observations-typed-p ()
  (forall (pointer index)
    (implies
     (and
      (mpsubn-pointer-p pointer)
      (integerp index))
     (mpsubn-bv64-p
      (mpsubn-pelt pointer index)))))

(defun mpsubn-interface-p ()
  (and
   (mpsubn-pointer-domain-nonempty-p)
   (mpsubn-zone-domain-nonempty-p)
   (mpsubn-interface-typed-p)
   (mpsubn-limb-observations-typed-p)))

;; Int.toNat is used only for source integer exponents and recursion counts.

(defun mpsubn-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

;; Little-endian radix-2^64 value over the total limb observation.

(defun mpsubn-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpsubn-pelt pointer index)
     (*
      18446744073709551616
      (mpsubn-value-from
       pointer
       (+ index 1)
       (- count 1))))))

(defun mpsubn-value (pointer size)
  (mpsubn-value-from
   pointer
   (mpsubn-offset pointer)
   (mpsubn-int-to-nat size)))

(defun mpsubn-radix-power (exponent)
  (expt
   18446744073709551616
   (mpsubn-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsubn-valid-p (pointer size)
  (and
   (mpsubn-pointer-p pointer)
   (mpsubn-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpsubn-minimum pointer))
   (<= (mpsubn-minimum pointer)
       (mpsubn-offset pointer))
   (<= (+ (mpsubn-offset pointer) size)
       (mpsubn-maximum pointer))
   (<= (mpsubn-maximum pointer)
       (mpsubn-data-length pointer))))

(defun mpsubn-copy-fields-p (new old)
  (and
   (equal
    (mpsubn-data-length new)
    (mpsubn-data-length old))
   (equal
    (mpsubn-offset new)
    (mpsubn-offset old))
   (equal
    (mpsubn-minimum new)
    (mpsubn-minimum old))
   (equal
    (mpsubn-maximum new)
    (mpsubn-maximum old))
   (equal
    (mpsubn-writable new)
    (mpsubn-writable old))
   (equal
    (mpsubn-zone new)
    (mpsubn-zone old))))

(defun mpsubn-valid-index-p (pointer index)
  (and
   (<= (mpsubn-minimum pointer)
       (+ (mpsubn-offset pointer) index))
   (< (+ (mpsubn-offset pointer) index)
      (mpsubn-maximum pointer))))

(defun mpsubn-borrow-range-p (borrow)
  (and
   (<= 0 borrow)
   (<= borrow 1)))

;; Equality on the source integer-indexed pelts maps.

(defun-sk mpsubn-tail-equal-p
    (new old from size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= from index)
       (< index size))
      (equal
       (mpsubn-pelt
        new
        (+ (mpsubn-offset new) index))
       (mpsubn-pelt
        old
        (+ (mpsubn-offset new) index)))))))

(defun-sk mpsubn-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpsubn-offset new))
       (<= (+ (mpsubn-offset new) size)
           index))
      (equal
       (mpsubn-pelt new index)
       (mpsubn-pelt old index))))))

(defun-sk mpsubn-single-update-p
    (new old update-index result)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsubn-pelt new index)
      (if (equal index update-index)
          result
        (mpsubn-pelt old index))))))

(defun mpsubn-value-equation-p
    (new old-x y size borrow)
  (equal
   (-
    (mpsubn-value new size)
    (*
     (mpsubn-radix-power size)
     borrow))
   (-
    (mpsubn-value old-x size)
    (mpsubn-value y size))))

(defun mpsubn-sub-with-borrow-p
    (memory y index incoming result borrow)
  (and
   (equal
    (-
     result
     (* 18446744073709551616 borrow))
    (-
     (-
      (mpsubn-pelt
       memory
       (+ (mpsubn-offset memory) index))
      (mpsubn-pelt
       y
       (+ (mpsubn-offset y) index)))
     incoming))
   (mpsubn-borrow-range-p borrow)))

(defun mpsubn-loop-invariant-p
    (memory old-x y size index borrow)
  (and
   (<= 0 index)
   (<= index size)
   (mpsubn-value-equation-p
    memory old-x y index borrow)
   (mpsubn-borrow-range-p borrow)
   (mpsubn-tail-equal-p
    memory old-x index size)
   (mpsubn-outside-equal-p
    memory old-x size)))

(defun mpsubn-next-invariant-p
    (memory old-x y size index borrow next-index)
  (and
   (<= 0 (- size index))
   (< (- size next-index)
      (- size index))
   (<= 0 next-index)
   (<= next-index size)
   (mpsubn-value-equation-p
    memory old-x y next-index borrow)
   (mpsubn-borrow-range-p borrow)
   (mpsubn-tail-equal-p
    memory old-x next-index size)
   (mpsubn-outside-equal-p
    memory old-x size)))

(defun-sk mpsubn-all-next-indices-p
    (memory old-x y size-word index-word borrow)
  (forall (next-index-word)
    (implies
     (mpsubn-bv32-p next-index-word)
     (implies
      (equal
       (mpsubn-signed32 next-index-word)
       (+ (mpsubn-signed32 index-word) 1))
      (mpsubn-next-invariant-p
       memory
       old-x
       y
       (mpsubn-signed32 size-word)
       (mpsubn-signed32 index-word)
       borrow
       (mpsubn-signed32 next-index-word))))))

(defun mpsubn-updated-memory-body-p
    (updated before old-x y size-word index-word result borrow)
  (implies
   (mpsubn-copy-fields-p updated before)
   (implies
    (and
     (mpsubn-single-update-p
      updated
      before
      (+ (mpsubn-offset updated)
         (mpsubn-signed32 index-word))
      result)
     (equal
      (mpsubn-pelt
       updated
       (+ (mpsubn-offset updated)
          (mpsubn-signed32 index-word)))
      result))
    (and
     (mpsubn-int32-in-bounds-p
      (+ (mpsubn-signed32 index-word) 1))
     (mpsubn-all-next-indices-p
      updated
      old-x
      y
      size-word
      index-word
      borrow)))))

(defun-sk mpsubn-all-updated-memories-p
    (before old-x y size-word index-word result borrow)
  (forall (updated)
    (implies
     (mpsubn-pointer-p updated)
     (mpsubn-updated-memory-body-p
      updated
      before
      old-x
      y
      size-word
      index-word
      result
      borrow))))

(defun mpsubn-result-borrow-body-p
    (memory old-x y size-word index-word incoming result borrow)
  (implies
   (mpsubn-sub-with-borrow-p
    memory
    y
    (mpsubn-signed32 index-word)
    incoming
    result
    borrow)
   (and
    (and
     (mpsubn-valid-index-p
      memory
      (mpsubn-signed32 index-word))
     (equal (mpsubn-writable memory) t))
    (mpsubn-all-updated-memories-p
     memory
     old-x
     y
     size-word
     index-word
     result
     borrow))))

(defun-sk mpsubn-all-result-borrow-p
    (memory old-x y size-word index-word incoming)
  (forall (result borrow)
    (implies
     (and
      (mpsubn-bv64-p result)
      (mpsubn-bv64-p borrow))
     (mpsubn-result-borrow-body-p
      memory
      old-x
      y
      size-word
      index-word
      incoming
      result
      borrow))))

(defun mpsubn-loop-branch-p
    (memory old-x y size-word index-word borrow)
  (if (< (mpsubn-signed32 index-word)
         (mpsubn-signed32 size-word))
      (and
       (mpsubn-valid-index-p
        memory
        (mpsubn-signed32 index-word))
       (mpsubn-valid-index-p
        y
        (mpsubn-signed32 index-word))
       (mpsubn-borrow-range-p borrow)
       (mpsubn-all-result-borrow-p
        memory
        old-x
        y
        size-word
        index-word
        borrow))
    (and
     (mpsubn-value-equation-p
      memory
      old-x
      y
      (mpsubn-signed32 size-word)
      borrow)
     (mpsubn-borrow-range-p borrow)
     (mpsubn-outside-equal-p
      memory
      old-x
      (mpsubn-signed32 size-word)))))

(defun mpsubn-loop-state-body-p
    (old-x y size-word index-word borrow memory)
  (implies
   (mpsubn-copy-fields-p memory old-x)
   (implies
    (mpsubn-loop-invariant-p
     memory
     old-x
     y
     (mpsubn-signed32 size-word)
     (mpsubn-signed32 index-word)
     borrow)
    (mpsubn-loop-branch-p
     memory
     old-x
     y
     size-word
     index-word
     borrow))))

(defun-sk mpsubn-all-loop-states-p
    (old-x y size-word)
  (forall (index-word borrow memory)
    (implies
     (and
      (mpsubn-bv32-p index-word)
      (mpsubn-bv64-p borrow)
      (mpsubn-pointer-p memory))
     (mpsubn-loop-state-body-p
      old-x
      y
      size-word
      index-word
      borrow
      memory))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-subold-wmpn-sub-n-in-placeqtvc-statement
    ()
  (forall (size-word x y)
    (implies
     (and
      (mpsubn-interface-p)
      (mpsubn-bv32-p size-word)
      (mpsubn-pointer-p x)
      (mpsubn-pointer-p y)
      (<= 0 (mpsubn-signed32 size-word))
      (mpsubn-valid-p
       x
       (mpsubn-signed32 size-word))
      (mpsubn-valid-p
       y
       (mpsubn-signed32 size-word))
      (equal (mpsubn-writable x) t))
     (and
      (<= 0 0)
      (<= 0 (mpsubn-signed32 size-word))
      (equal
       (-
        (mpsubn-value x 0)
        (* (mpsubn-radix-power 0) 0))
       (-
        (mpsubn-value x 0)
        (mpsubn-value y 0)))
      (<= 0 0)
      (<= 0 1)
      (mpsubn-all-loop-states-p
       x
       y
       size-word)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
