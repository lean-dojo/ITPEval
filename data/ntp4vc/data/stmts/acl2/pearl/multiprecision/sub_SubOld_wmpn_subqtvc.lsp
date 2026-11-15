;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_SubOld_wmpn_subqtvc: the verification condition
;; for unequal-length multiprecision subtraction into a separate result
;; pointer, including borrow propagation, limb copying, pointer updates, and
;; frame preservation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical unsigned representatives are in bijection with the source
;; fixed-width words. Signed conversion is two's-complement interpretation.

(defun mpsub-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpsub-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpsub-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpsub-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones are arbitrary inhabited source carrier types. Pointer
;; length and the total integer-indexed limb observation are independent
;; selectors, matching the primary Why3 array model.

(defstub mpsub-pointer-p (pointer) t)
(defstub mpsub-zone-p (zone) t)
(defstub mpsub-data-length (pointer) t)
(defstub mpsub-pelt (pointer index) t)
(defstub mpsub-offset (pointer) t)
(defstub mpsub-minimum (pointer) t)
(defstub mpsub-maximum (pointer) t)
(defstub mpsub-writable (pointer) t)
(defstub mpsub-zone (pointer) t)

(defun-sk mpsub-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpsub-pointer-p pointer)))

(defun-sk mpsub-zone-domain-nonempty-p ()
  (exists (zone)
    (mpsub-zone-p zone)))

(defun-sk mpsub-interface-typed-p ()
  (forall (pointer)
    (implies
     (mpsub-pointer-p pointer)
     (and
      (integerp (mpsub-data-length pointer))
      (<= 0 (mpsub-data-length pointer))
      (integerp (mpsub-offset pointer))
      (integerp (mpsub-minimum pointer))
      (integerp (mpsub-maximum pointer))
      (booleanp (mpsub-writable pointer))
      (mpsub-zone-p
       (mpsub-zone pointer))))))

(defun-sk mpsub-limb-observations-typed-p ()
  (forall (pointer index)
    (implies
     (and
      (mpsub-pointer-p pointer)
      (integerp index))
     (mpsub-bv64-p
      (mpsub-pelt pointer index)))))

(defun mpsub-interface-p ()
  (and
   (mpsub-pointer-domain-nonempty-p)
   (mpsub-zone-domain-nonempty-p)
   (mpsub-interface-typed-p)
   (mpsub-limb-observations-typed-p)))

;; Int.toNat is used for source integer exponents and recursion counts.

(defun mpsub-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

;; Little-endian radix-2^64 value over the total limb observation.

(defun mpsub-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpsub-pelt pointer index)
     (*
      18446744073709551616
      (mpsub-value-from
       pointer
       (+ index 1)
       (- count 1))))))

(defun mpsub-value (pointer size)
  (mpsub-value-from
   pointer
   (mpsub-offset pointer)
   (mpsub-int-to-nat size)))

(defun mpsub-radix-power (exponent)
  (expt
   18446744073709551616
   (mpsub-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsub-valid-p (pointer size)
  (and
   (mpsub-pointer-p pointer)
   (mpsub-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpsub-minimum pointer))
   (<= (mpsub-minimum pointer)
       (mpsub-offset pointer))
   (<= (+ (mpsub-offset pointer) size)
       (mpsub-maximum pointer))
   (<= (mpsub-maximum pointer)
       (mpsub-data-length pointer))))

(defun mpsub-copy-fields-p (new old)
  (and
   (equal
    (mpsub-data-length new)
    (mpsub-data-length old))
   (equal
    (mpsub-offset new)
    (mpsub-offset old))
   (equal
    (mpsub-minimum new)
    (mpsub-minimum old))
   (equal
    (mpsub-maximum new)
    (mpsub-maximum old))
   (equal
    (mpsub-writable new)
    (mpsub-writable old))
   (equal
    (mpsub-zone new)
    (mpsub-zone old))))

(defun mpsub-valid-index-p (pointer index)
  (and
   (<= (mpsub-minimum pointer)
       (+ (mpsub-offset pointer) index))
   (< (+ (mpsub-offset pointer) index)
      (mpsub-maximum pointer))))

(defun mpsub-borrow-range-p (borrow)
  (and
   (<= 0 borrow)
   (<= borrow 1)))

;; Equality outside the original result interval.

(defun-sk mpsub-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpsub-offset new))
       (<= (+ (mpsub-offset new) size)
           index))
      (equal
       (mpsub-pelt new index)
       (mpsub-pelt old index))))))

;; Extensional equality with the single map update appearing in the source.

(defun-sk mpsub-single-update-p
    (new old update-index result)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsub-pelt new index)
      (if (equal index update-index)
          result
        (mpsub-pelt old index))))))

(defun mpsub-value-equation-p
    (memory x y size y-size borrow)
  (equal
   (-
    (mpsub-value memory size)
    (*
     (mpsub-radix-power size)
     borrow))
   (-
    (mpsub-value x size)
    (mpsub-value y y-size))))

;; The second loop copies the remaining limbs of x into the result.

(defun mpsub-copy-next-invariant-p
    (memory original-result x y
            sy sx index borrow next-index)
  (and
   (<= 0 (- sx index))
   (< (- sx next-index)
      (- sx index))
   (<= sy next-index)
   (<= next-index sx)
   (or
    (equal next-index sx)
    (equal borrow 0))
   (mpsub-value-equation-p
    memory x y next-index sy borrow)
   (mpsub-outside-equal-p
    memory original-result sx)))

(defun-sk mpsub-all-copy-next-indices-p
    (memory original-result x y
            sy-word sx-word index-word borrow)
  (forall (next-index-word)
    (implies
     (mpsub-bv32-p next-index-word)
     (implies
      (equal
       (mpsub-signed32 next-index-word)
       (+ (mpsub-signed32 index-word) 1))
      (mpsub-copy-next-invariant-p
       memory
       original-result
       x
       y
       (mpsub-signed32 sy-word)
       (mpsub-signed32 sx-word)
       (mpsub-signed32 index-word)
       borrow
       (mpsub-signed32 next-index-word))))))

(defun mpsub-copy-updated-body-p
    (updated before original-result x y
             sy-word sx-word index-word borrow)
  (implies
   (mpsub-copy-fields-p updated before)
   (implies
    (and
     (mpsub-single-update-p
      updated
      before
      (+ (mpsub-offset updated)
         (mpsub-signed32 index-word))
      (mpsub-pelt
       x
       (+ (mpsub-offset x)
          (mpsub-signed32 index-word))))
     (equal
      (mpsub-pelt
       updated
       (+ (mpsub-offset updated)
          (mpsub-signed32 index-word)))
      (mpsub-pelt
       x
       (+ (mpsub-offset x)
          (mpsub-signed32 index-word)))))
    (and
     (mpsub-int32-in-bounds-p
      (+ (mpsub-signed32 index-word) 1))
     (mpsub-all-copy-next-indices-p
      updated
      original-result
      x
      y
      sy-word
      sx-word
      index-word
      borrow)))))

(defun-sk mpsub-all-copy-updated-p
    (before original-result x y
            sy-word sx-word index-word borrow)
  (forall (updated)
    (implies
     (mpsub-pointer-p updated)
     (mpsub-copy-updated-body-p
      updated
      before
      original-result
      x
      y
      sy-word
      sx-word
      index-word
      borrow))))

(defun mpsub-copy-loop-branch-p
    (memory original-result x y
            sy-word sx-word index-word borrow)
  (if (< (mpsub-signed32 index-word)
         (mpsub-signed32 sx-word))
      (and
       (mpsub-valid-index-p
        x
        (mpsub-signed32 index-word))
       (and
        (mpsub-valid-index-p
         memory
         (mpsub-signed32 index-word))
        (equal (mpsub-writable memory) t))
       (mpsub-all-copy-updated-p
        memory
        original-result
        x
        y
        sy-word
        sx-word
        index-word
        borrow))
    (and
     (mpsub-value-equation-p
      memory
      x
      y
      (mpsub-signed32 sx-word)
      (mpsub-signed32 sy-word)
      borrow)
     (mpsub-outside-equal-p
      memory
      original-result
      (mpsub-signed32 sx-word))
     (mpsub-borrow-range-p borrow))))

(defun mpsub-copy-loop-state-body-p
    (original-result x y sy-word sx-word
                     base index-word borrow memory)
  (implies
   (mpsub-copy-fields-p memory base)
   (implies
    (and
     (<= (mpsub-signed32 sy-word)
         (mpsub-signed32 index-word))
     (<= (mpsub-signed32 index-word)
         (mpsub-signed32 sx-word))
     (or
      (equal index-word sx-word)
      (equal borrow 0))
     (mpsub-value-equation-p
      memory
      x
      y
      (mpsub-signed32 index-word)
      (mpsub-signed32 sy-word)
      borrow)
     (mpsub-outside-equal-p
      memory
      original-result
      (mpsub-signed32 sx-word)))
    (mpsub-copy-loop-branch-p
     memory
     original-result
     x
     y
     sy-word
     sx-word
     index-word
     borrow))))

(defun-sk mpsub-all-copy-loop-states-p
    (original-result x y sy-word sx-word base borrow)
  (forall (index-word memory)
    (implies
     (and
      (mpsub-bv32-p index-word)
      (mpsub-pointer-p memory))
     (mpsub-copy-loop-state-body-p
      original-result
      x
      y
      sy-word
      sx-word
      base
      index-word
      borrow
      memory))))

;; The first loop propagates a nonzero borrow by subtracting one from x limbs.

(defun mpsub-borrow-o4-body-p
    (original-result sy-word sx-word x y
                     index-word borrow after
                     next-index-word test)
  (implies
   (and
    (implies
     (equal
      (mpsub-pelt
       x
       (+ (mpsub-offset x)
          (mpsub-signed32 index-word)))
      0)
     (equal test t))
    (implies
     (equal test t)
     (equal
      (mpsub-pelt
       x
       (+ (mpsub-offset x)
          (mpsub-signed32 index-word)))
      0)))
   (if (not (equal test t))
       (and
        (<= (mpsub-signed32 sy-word)
            (mpsub-signed32 next-index-word))
        (<= (mpsub-signed32 next-index-word)
            (mpsub-signed32 sx-word))
        (or
         (equal next-index-word sx-word)
         (equal 0 0))
        (mpsub-value-equation-p
         after
         x
         y
         (mpsub-signed32 next-index-word)
         (mpsub-signed32 sy-word)
         0)
        (mpsub-outside-equal-p
         after
         original-result
         (mpsub-signed32 sx-word))
        (mpsub-all-copy-loop-states-p
         original-result
         x
         y
         sy-word
         sx-word
         after
         0))
     (and
      (<= 0
          (- (mpsub-signed32 sx-word)
             (mpsub-signed32 index-word)))
      (< (- (mpsub-signed32 sx-word)
            (mpsub-signed32 next-index-word))
         (- (mpsub-signed32 sx-word)
            (mpsub-signed32 index-word)))
      (<= (mpsub-signed32 sy-word)
          (mpsub-signed32 next-index-word))
      (<= (mpsub-signed32 next-index-word)
          (mpsub-signed32 sx-word))
      (mpsub-value-equation-p
       after
       x
       y
       (mpsub-signed32 next-index-word)
       (mpsub-signed32 sy-word)
       borrow)
      (mpsub-outside-equal-p
       after
       original-result
       (mpsub-signed32 sx-word))
      (mpsub-borrow-range-p borrow)
      (or
       (equal next-index-word sx-word)
       (equal borrow 1))))))

(defun-sk mpsub-all-borrow-o4-p
    (original-result sy-word sx-word x y
                     index-word borrow after
                     next-index-word)
  (forall (test)
    (implies
     (booleanp test)
     (mpsub-borrow-o4-body-p
      original-result
      sy-word
      sx-word
      x
      y
      index-word
      borrow
      after
      next-index-word
      test))))

(defun-sk mpsub-all-borrow-next-indices-p
    (original-result sy-word sx-word x y
                     index-word borrow after)
  (forall (next-index-word)
    (implies
     (mpsub-bv32-p next-index-word)
     (implies
      (equal
       (mpsub-signed32 next-index-word)
       (+ (mpsub-signed32 index-word) 1))
      (mpsub-all-borrow-o4-p
       original-result
       sy-word
       sx-word
       x
       y
       index-word
       borrow
       after
       next-index-word)))))

(defun mpsub-borrow-updated-body-p
    (updated before original-result x y
             sy-word sx-word index-word borrow result)
  (implies
   (mpsub-copy-fields-p updated before)
   (implies
    (and
     (mpsub-single-update-p
      updated
      before
      (+ (mpsub-offset updated)
         (mpsub-signed32 index-word))
      result)
     (equal
      (mpsub-pelt
       updated
       (+ (mpsub-offset updated)
          (mpsub-signed32 index-word)))
      result))
    (and
     (mpsub-int32-in-bounds-p
      (+ (mpsub-signed32 index-word) 1))
     (mpsub-all-borrow-next-indices-p
      original-result
      sy-word
      sx-word
      x
      y
      index-word
      borrow
      updated)))))

(defun-sk mpsub-all-borrow-updated-p
    (before original-result x y
            sy-word sx-word index-word borrow result)
  (forall (updated)
    (implies
     (mpsub-pointer-p updated)
     (mpsub-borrow-updated-body-p
      updated
      before
      original-result
      x
      y
      sy-word
      sx-word
      index-word
      borrow
      result))))

(defun mpsub-borrow-result-body-p
    (memory original-result x y
            sy-word sx-word index-word borrow result)
  (implies
   (equal
    result
    (mod
     (-
      (mpsub-pelt
       x
       (+ (mpsub-offset x)
          (mpsub-signed32 index-word)))
      1)
     18446744073709551616))
   (and
    (and
     (mpsub-valid-index-p
      memory
      (mpsub-signed32 index-word))
     (equal (mpsub-writable memory) t))
    (mpsub-all-borrow-updated-p
     memory
     original-result
     x
     y
     sy-word
     sx-word
     index-word
     borrow
     result))))

(defun-sk mpsub-all-borrow-results-p
    (memory original-result x y
            sy-word sx-word index-word borrow)
  (forall (result)
    (implies
     (mpsub-bv64-p result)
     (mpsub-borrow-result-body-p
      memory
      original-result
      x
      y
      sy-word
      sx-word
      index-word
      borrow
      result))))

(defun mpsub-borrow-loop-branch-p
    (memory original-result x y
            sy-word sx-word index-word borrow)
  (if (< (mpsub-signed32 index-word)
         (mpsub-signed32 sx-word))
      (and
       (mpsub-valid-index-p
        x
        (mpsub-signed32 index-word))
       (mpsub-all-borrow-results-p
        memory
        original-result
        x
        y
        sy-word
        sx-word
        index-word
        borrow))
    (and
     (<= (mpsub-signed32 sy-word)
         (mpsub-signed32 index-word))
     (<= (mpsub-signed32 index-word)
         (mpsub-signed32 sx-word))
     (or
      (equal index-word sx-word)
      (equal borrow 0))
     (mpsub-value-equation-p
      memory
      x
      y
      (mpsub-signed32 index-word)
      (mpsub-signed32 sy-word)
      borrow)
     (mpsub-outside-equal-p
      memory
      original-result
      (mpsub-signed32 sx-word))
     (mpsub-borrow-range-p borrow)
     (mpsub-all-copy-loop-states-p
      original-result
      x
      y
      sy-word
      sx-word
      memory
      borrow))))

(defun mpsub-borrow-loop-state-body-p
    (original-result x y sy-word sx-word
                     base index-word borrow memory)
  (implies
   (mpsub-copy-fields-p memory base)
   (implies
    (and
     (<= (mpsub-signed32 sy-word)
         (mpsub-signed32 index-word))
     (<= (mpsub-signed32 index-word)
         (mpsub-signed32 sx-word))
     (mpsub-value-equation-p
      memory
      x
      y
      (mpsub-signed32 index-word)
      (mpsub-signed32 sy-word)
      borrow)
     (mpsub-outside-equal-p
      memory
      original-result
      (mpsub-signed32 sx-word))
     (mpsub-borrow-range-p borrow)
     (or
      (equal index-word sx-word)
      (equal borrow 1)))
    (mpsub-borrow-loop-branch-p
     memory
     original-result
     x
     y
     sy-word
     sx-word
     index-word
     borrow))))

(defun-sk mpsub-all-borrow-loop-states-p
    (original-result x y sy-word sx-word base)
  (forall (index-word borrow memory)
    (implies
     (and
      (mpsub-bv32-p index-word)
      (mpsub-bv64-p borrow)
      (mpsub-pointer-p memory))
     (mpsub-borrow-loop-state-body-p
      original-result
      x
      y
      sy-word
      sx-word
      base
      index-word
      borrow
      memory))))

;; Continuation after the initial equal-length subtraction.

(defun mpsub-initial-test-body-p
    (original-result sy-word sx-word x y
                     first-result borrow test)
  (implies
   (and
    (implies
     (equal borrow 0)
     (equal test t))
    (implies
     (equal test t)
     (equal borrow 0)))
   (if (not (equal test t))
       (and
        (<= (mpsub-signed32 sy-word)
            (mpsub-signed32 sy-word))
        (<= (mpsub-signed32 sy-word)
            (mpsub-signed32 sx-word))
        (mpsub-value-equation-p
         first-result
         x
         y
         (mpsub-signed32 sy-word)
         (mpsub-signed32 sy-word)
         borrow)
        (mpsub-outside-equal-p
         first-result
         original-result
         (mpsub-signed32 sx-word))
        (mpsub-borrow-range-p borrow)
        (or
         (equal sy-word sx-word)
         (equal borrow 1))
        (mpsub-all-borrow-loop-states-p
         original-result
         x
         y
         sy-word
         sx-word
         first-result))
     (and
      (<= (mpsub-signed32 sy-word)
          (mpsub-signed32 sy-word))
      (<= (mpsub-signed32 sy-word)
          (mpsub-signed32 sx-word))
      (or
       (equal sy-word sx-word)
       (equal borrow 0))
      (mpsub-value-equation-p
       first-result
       x
       y
       (mpsub-signed32 sy-word)
       (mpsub-signed32 sy-word)
       borrow)
      (mpsub-outside-equal-p
       first-result
       original-result
       (mpsub-signed32 sx-word))
      (mpsub-all-copy-loop-states-p
       original-result
       x
       y
       sy-word
       sx-word
       first-result
       borrow)))))

(defun-sk mpsub-all-initial-tests-p
    (original-result sy-word sx-word x y first-result borrow)
  (forall (test)
    (implies
     (booleanp test)
     (mpsub-initial-test-body-p
      original-result
      sy-word
      sx-word
      x
      y
      first-result
      borrow
      test))))

(defun mpsub-initial-borrow-body-p
    (original-result sy-word sx-word x y first-result borrow)
  (implies
   (and
    (mpsub-borrow-range-p borrow)
    (mpsub-value-equation-p
     first-result
     x
     y
     (mpsub-signed32 sy-word)
     (mpsub-signed32 sy-word)
     borrow)
    (mpsub-outside-equal-p
     first-result
     original-result
     (mpsub-signed32 sy-word)))
   (mpsub-all-initial-tests-p
    original-result
    sy-word
    sx-word
    x
    y
    first-result
    borrow)))

(defun-sk mpsub-all-initial-borrows-p
    (original-result sy-word sx-word x y first-result)
  (forall (borrow)
    (implies
     (mpsub-bv64-p borrow)
     (mpsub-initial-borrow-body-p
      original-result
      sy-word
      sx-word
      x
      y
      first-result
      borrow))))

(defun mpsub-first-result-body-p
    (original-result sy-word sx-word x y first-result)
  (implies
   (mpsub-copy-fields-p first-result original-result)
   (mpsub-all-initial-borrows-p
    original-result
    sy-word
    sx-word
    x
    y
    first-result)))

(defun-sk mpsub-all-first-results-p
    (original-result sy-word sx-word x y)
  (forall (first-result)
    (implies
     (mpsub-pointer-p first-result)
     (mpsub-first-result-body-p
      original-result
      sy-word
      sx-word
      x
      y
      first-result))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-subold-wmpn-subqtvc-statement
    ()
  (forall (sy-word sx-word x y result-pointer)
    (implies
     (and
      (mpsub-interface-p)
      (mpsub-bv32-p sy-word)
      (mpsub-bv32-p sx-word)
      (mpsub-pointer-p x)
      (mpsub-pointer-p y)
      (mpsub-pointer-p result-pointer)
      (<= 0 (mpsub-signed32 sy-word))
      (<= (mpsub-signed32 sy-word)
          (mpsub-signed32 sx-word))
      (mpsub-valid-p
       x
       (mpsub-signed32 sx-word))
      (mpsub-valid-p
       y
       (mpsub-signed32 sy-word))
      (mpsub-valid-p
       result-pointer
       (mpsub-signed32 sx-word))
      (equal (mpsub-writable result-pointer) t))
     (and
      (mpsub-valid-p
       x
       (mpsub-signed32 sy-word))
      (mpsub-valid-p
       y
       (mpsub-signed32 sy-word))
      (mpsub-valid-p
       result-pointer
       (mpsub-signed32 sy-word))
      (equal (mpsub-writable result-pointer) t)
      (mpsub-all-first-results-p
       result-pointer
       sy-word
       sx-word
       x
       y)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
