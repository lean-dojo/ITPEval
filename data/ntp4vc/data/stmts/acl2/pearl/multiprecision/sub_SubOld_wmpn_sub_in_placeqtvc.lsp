;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_SubOld_wmpn_sub_in_placeqtvc: the verification
;; condition for in-place unequal-length multi-precision subtraction, including
;; borrow propagation, pointer validity, and frame preservation. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical unsigned representatives are in bijection with the source
;; fixed-width words. Signed conversion is two's-complement interpretation.

(defun mp-sub-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mp-sub-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mp-sub-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mp-sub-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones are the source's arbitrary inhabited carrier types.
;; Pointer length and the total integer-indexed limb observation are independent
;; selectors, matching the two ways the source VC observes pointer memory.
;; The statement predicate makes nonemptiness and every typing law explicit.

(defstub mp-sub-ptr64-p (pointer) t)
(defstub mp-sub-zone-p (zone) t)
(defstub mp-sub-ptr-length (pointer) t)
(defstub mp-sub-ptr-limb (pointer index) t)
(defstub mp-sub-ptr-offset (pointer) t)
(defstub mp-sub-ptr-min (pointer) t)
(defstub mp-sub-ptr-max (pointer) t)
(defstub mp-sub-ptr-writable (pointer) t)
(defstub mp-sub-ptr-zone (pointer) t)

(defun-sk mp-sub-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mp-sub-ptr64-p pointer)))

(defun-sk mp-sub-zone-domain-nonempty-p ()
  (exists (zone)
    (mp-sub-zone-p zone)))

(defun-sk mp-sub-pointer-selectors-typed-p ()
  (forall (pointer)
    (implies
     (mp-sub-ptr64-p pointer)
     (and
      (integerp (mp-sub-ptr-length pointer))
      (<= 0 (mp-sub-ptr-length pointer))
      (integerp (mp-sub-ptr-offset pointer))
      (integerp (mp-sub-ptr-min pointer))
      (integerp (mp-sub-ptr-max pointer))
      (booleanp (mp-sub-ptr-writable pointer))
      (mp-sub-zone-p (mp-sub-ptr-zone pointer))))))

(defun-sk mp-sub-limb-observations-typed-p ()
  (forall (pointer index)
    (implies
     (and
      (mp-sub-ptr64-p pointer)
      (integerp index))
     (mp-sub-bv64-p
      (mp-sub-ptr-limb pointer index)))))

(defun mp-sub-pointer-interface-p ()
  (and
   (mp-sub-pointer-domain-nonempty-p)
   (mp-sub-zone-domain-nonempty-p)
   (mp-sub-pointer-selectors-typed-p)
   (mp-sub-limb-observations-typed-p)))

;; Int.toNat is used only for source integer exponents and recursion counts.

(defun mp-sub-int-to-nat (value)
  (if (and (integerp value)
           (< value 0))
      0
    (nfix value)))

(defun mp-sub-pelts (pointer index)
  (mp-sub-ptr-limb pointer index))

;; Little-endian radix-2^64 value. The count is Int.toNat(size), matching the
;; source value_sub recursion over the total integer-indexed limb observation.

(defun mp-sub-value-count (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (mp-sub-pelts pointer index)
       (* 18446744073709551616
          (mp-sub-value-count
           pointer
           (+ 1 index)
           (- count 1))))))

(defun mp-sub-value (pointer size)
  (mp-sub-value-count
   pointer
   (mp-sub-ptr-offset pointer)
   (mp-sub-int-to-nat size)))

(defun mp-sub-radix-power (exponent)
  (expt
   18446744073709551616
   (mp-sub-int-to-nat exponent)))

;; This is C.valid, including the signed-32 size bounds and pointer interval.

(defun mp-sub-valid-p (pointer size)
  (and
   (mp-sub-ptr64-p pointer)
   (mp-sub-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mp-sub-ptr-min pointer))
   (<= (mp-sub-ptr-min pointer)
       (mp-sub-ptr-offset pointer))
   (<= (+ (mp-sub-ptr-offset pointer) size)
       (mp-sub-ptr-max pointer))
   (<= (mp-sub-ptr-max pointer)
       (mp-sub-ptr-length pointer))))

(defun mp-sub-copy-fields-p (new old)
  (and
   (equal (mp-sub-ptr-length new)
          (mp-sub-ptr-length old))
   (equal (mp-sub-ptr-offset new)
          (mp-sub-ptr-offset old))
   (equal (mp-sub-ptr-min new)
          (mp-sub-ptr-min old))
   (equal (mp-sub-ptr-max new)
          (mp-sub-ptr-max old))
   (equal (mp-sub-ptr-writable new)
          (mp-sub-ptr-writable old))
   (equal (mp-sub-ptr-zone new)
          (mp-sub-ptr-zone old))))

(defun-sk mp-sub-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mp-sub-ptr-offset new))
       (<= (+ (mp-sub-ptr-offset new) size)
           index))
      (equal
       (mp-sub-pelts new index)
       (mp-sub-pelts old index))))))

(defun-sk mp-sub-tail-equal-p
    (new old from size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= from index)
       (< index size))
      (equal
       (mp-sub-pelts
        new
        (+ (mp-sub-ptr-offset new) index))
       (mp-sub-pelts
        old
        (+ (mp-sub-ptr-offset new) index)))))))

;; Extensional equality with the single map update appearing in the source.

(defun-sk mp-sub-pelts-update-p
    (new old update-index result)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mp-sub-pelts new index)
      (if (equal index update-index)
          result
        (mp-sub-pelts old index))))))

(defun mp-sub-value-equation-p
    (new old-x y size y-size borrow)
  (equal
   (- (mp-sub-value new size)
      (* (mp-sub-radix-power size)
         borrow))
   (- (mp-sub-value old-x size)
      (mp-sub-value y y-size))))

(defun mp-sub-borrow-range-p (borrow)
  (and
   (<= 0 borrow)
   (<= borrow 1)))

;; The following predicates preserve the VC's nested universal continuations
;; from the innermost Boolean equality test outward.

(defun mp-sub-o4-body-p
    (sy sx x y i c x2 x3 o3 o4)
  (implies
   (and
    (implies
     (equal
      (mp-sub-pelts
       x2
       (+ (mp-sub-ptr-offset x2)
          (mp-sub-signed32 i)))
      0)
     (equal o4 t))
    (implies
     (equal o4 t)
     (equal
      (mp-sub-pelts
       x2
       (+ (mp-sub-ptr-offset x2)
          (mp-sub-signed32 i)))
      0)))
   (if (not (equal o4 t))
       (and
        (mp-sub-value-equation-p
         x3 x y
         (mp-sub-signed32 sx)
         (mp-sub-signed32 sy)
         0)
        (mp-sub-borrow-range-p 0)
        (mp-sub-outside-equal-p
         x3 x (mp-sub-signed32 sx)))
     (and
      (<= 0
          (- (mp-sub-signed32 sx)
             (mp-sub-signed32 i)))
      (< (- (mp-sub-signed32 sx)
            (mp-sub-signed32 o3))
         (- (mp-sub-signed32 sx)
            (mp-sub-signed32 i)))
      (<= (mp-sub-signed32 sy)
          (mp-sub-signed32 o3))
      (<= (mp-sub-signed32 o3)
          (mp-sub-signed32 sx))
      (mp-sub-value-equation-p
       x3 x y
       (mp-sub-signed32 o3)
       (mp-sub-signed32 sy)
       c)
      (mp-sub-borrow-range-p c)
      (or
       (equal o3 sx)
       (equal c 1))
      (mp-sub-tail-equal-p
       x3 x
       (mp-sub-signed32 o3)
       (mp-sub-signed32 sx))
      (mp-sub-outside-equal-p
       x3 x (mp-sub-signed32 sx))))))

(defun-sk mp-sub-all-o4-p
    (sy sx x y i c x2 x3 o3)
  (forall (o4)
    (implies
     (booleanp o4)
     (mp-sub-o4-body-p
      sy sx x y i c x2 x3 o3 o4))))

(defun-sk mp-sub-all-o3-p
    (sy sx x y i c x2 x3)
  (forall (o3)
    (implies
     (mp-sub-bv32-p o3)
     (implies
      (equal
       (mp-sub-signed32 o3)
       (+ (mp-sub-signed32 i) 1))
      (mp-sub-all-o4-p
       sy sx x y i c x2 x3 o3)))))

(defun mp-sub-x3-body-p
    (sy sx x y i c x2 res x3)
  (implies
   (mp-sub-copy-fields-p x3 x2)
   (implies
    (and
     (mp-sub-pelts-update-p
      x3
      x2
      (+ (mp-sub-ptr-offset x3)
         (mp-sub-signed32 i))
      res)
     (equal
      (mp-sub-pelts
       x3
       (+ (mp-sub-ptr-offset x3)
          (mp-sub-signed32 i)))
      res))
    (and
     (mp-sub-int32-in-bounds-p
      (+ (mp-sub-signed32 i) 1))
     (mp-sub-all-o3-p
      sy sx x y i c x2 x3)))))

(defun-sk mp-sub-all-x3-p
    (sy sx x y i c x2 res)
  (forall (x3)
    (implies
     (mp-sub-ptr64-p x3)
     (mp-sub-x3-body-p
      sy sx x y i c x2 res x3))))

(defun mp-sub-res-body-p
    (sy sx x y i c x2 res)
  (implies
   (equal
    res
    (mod
     (- (mp-sub-pelts
         x2
         (+ (mp-sub-ptr-offset x2)
            (mp-sub-signed32 i)))
        1)
     18446744073709551616))
   (and
    (<= (mp-sub-ptr-min x2)
        (+ (mp-sub-ptr-offset x2)
           (mp-sub-signed32 i)))
    (< (+ (mp-sub-ptr-offset x2)
          (mp-sub-signed32 i))
       (mp-sub-ptr-max x2))
    (equal (mp-sub-ptr-writable x2) t)
    (mp-sub-all-x3-p
     sy sx x y i c x2 res))))

(defun-sk mp-sub-all-res-p
    (sy sx x y i c x2)
  (forall (res)
    (implies
     (mp-sub-bv64-p res)
     (mp-sub-res-body-p
      sy sx x y i c x2 res))))

(defun mp-sub-i-loop-body-p
    (sy sx x y x1 i c x2)
  (implies
   (mp-sub-copy-fields-p x2 x1)
   (implies
    (and
     (<= (mp-sub-signed32 sy)
         (mp-sub-signed32 i))
     (<= (mp-sub-signed32 i)
         (mp-sub-signed32 sx))
     (mp-sub-value-equation-p
      x2 x y
      (mp-sub-signed32 i)
      (mp-sub-signed32 sy)
      c)
     (mp-sub-borrow-range-p c)
     (or
      (equal i sx)
      (equal c 1))
     (mp-sub-tail-equal-p
      x2 x
      (mp-sub-signed32 i)
      (mp-sub-signed32 sx))
     (mp-sub-outside-equal-p
      x2 x (mp-sub-signed32 sx)))
    (if (< (mp-sub-signed32 i)
           (mp-sub-signed32 sx))
        (and
         (<= (mp-sub-ptr-min x2)
             (+ (mp-sub-ptr-offset x2)
                (mp-sub-signed32 i)))
         (< (+ (mp-sub-ptr-offset x2)
               (mp-sub-signed32 i))
            (mp-sub-ptr-max x2))
         (mp-sub-all-res-p
          sy sx x y i c x2))
      (and
       (mp-sub-value-equation-p
        x2 x y
        (mp-sub-signed32 sx)
        (mp-sub-signed32 sy)
        c)
       (mp-sub-borrow-range-p c)
       (mp-sub-outside-equal-p
        x2 x (mp-sub-signed32 sx)))))))

(defun-sk mp-sub-all-i-loop-p
    (sy sx x y x1)
  (forall (i c x2)
    (implies
     (and
      (mp-sub-bv32-p i)
      (mp-sub-bv64-p c)
      (mp-sub-ptr64-p x2))
     (mp-sub-i-loop-body-p
      sy sx x y x1 i c x2))))

(defun mp-sub-o2-body-p
    (sy sx x y x1 o1 o2)
  (implies
   (and
    (implies
     (equal o1 0)
     (equal o2 t))
    (implies
     (equal o2 t)
     (equal o1 0)))
   (if (not (equal o2 t))
       (and
        (and
         (<= (mp-sub-signed32 sy)
             (mp-sub-signed32 sy))
         (<= (mp-sub-signed32 sy)
             (mp-sub-signed32 sx)))
        (mp-sub-value-equation-p
         x1 x y
         (mp-sub-signed32 sy)
         (mp-sub-signed32 sy)
         o1)
        (mp-sub-borrow-range-p o1)
        (or
         (equal sy sx)
         (equal o1 1))
        (mp-sub-tail-equal-p
         x1 x
         (mp-sub-signed32 sy)
         (mp-sub-signed32 sx))
        (mp-sub-outside-equal-p
         x1 x (mp-sub-signed32 sx))
        (mp-sub-all-i-loop-p
         sy sx x y x1))
     (and
      (mp-sub-value-equation-p
       x1 x y
       (mp-sub-signed32 sx)
       (mp-sub-signed32 sy)
       o1)
      (mp-sub-borrow-range-p o1)
      (mp-sub-outside-equal-p
       x1 x (mp-sub-signed32 sx))))))

(defun-sk mp-sub-all-o2-p
    (sy sx x y x1 o1)
  (forall (o2)
    (implies
     (booleanp o2)
     (mp-sub-o2-body-p
      sy sx x y x1 o1 o2))))

(defun mp-sub-o1-body-p
    (sy sx x y x1 o1)
  (implies
   (and
    (mp-sub-borrow-range-p o1)
    (mp-sub-value-equation-p
     x1 x y
     (mp-sub-signed32 sy)
     (mp-sub-signed32 sy)
     o1)
    (mp-sub-outside-equal-p
     x1 x (mp-sub-signed32 sy)))
   (mp-sub-all-o2-p
    sy sx x y x1 o1)))

(defun-sk mp-sub-all-o1-p
    (sy sx x y x1)
  (forall (o1)
    (implies
     (mp-sub-bv64-p o1)
     (mp-sub-o1-body-p
      sy sx x y x1 o1))))

(defun mp-sub-x1-body-p
    (sy sx x y x1)
  (implies
   (mp-sub-copy-fields-p x1 x)
   (mp-sub-all-o1-p
    sy sx x y x1)))

(defun-sk mp-sub-all-x1-p
    (sy sx x y)
  (forall (x1)
    (implies
     (mp-sub-ptr64-p x1)
     (mp-sub-x1-body-p
      sy sx x y x1))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-subold-wmpn-sub-in-placeqtvc-statement
    ()
  (forall (sy sx x y)
    (implies
     (and
      (mp-sub-pointer-interface-p)
      (mp-sub-bv32-p sy)
      (mp-sub-bv32-p sx)
      (mp-sub-ptr64-p x)
      (mp-sub-ptr64-p y)
      (<= 0 (mp-sub-signed32 sy))
      (<= (mp-sub-signed32 sy)
          (mp-sub-signed32 sx))
      (mp-sub-valid-p
       x (mp-sub-signed32 sx))
      (mp-sub-valid-p
       y (mp-sub-signed32 sy))
      (equal (mp-sub-ptr-writable x) t))
     (and
      (<= 0 (mp-sub-signed32 sy))
      (mp-sub-valid-p
       x (mp-sub-signed32 sy))
      (mp-sub-valid-p
       y (mp-sub-signed32 sy))
      (equal (mp-sub-ptr-writable x) t)
      (mp-sub-all-x1-p
       sy sx x y)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
