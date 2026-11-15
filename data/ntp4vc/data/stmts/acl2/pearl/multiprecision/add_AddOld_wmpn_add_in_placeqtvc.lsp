;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/add_AddOld_wmpn_add_in_placeqtvc: the verification
;; condition for in-place unequal-length multi-precision addition, including
;; carry propagation, pointer validity, and frame preservation. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical unsigned representatives are in bijection with the source
;; fixed-width words. Signed conversion is two's-complement interpretation.

(defun mp-add-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mp-add-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mp-add-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mp-add-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones are the source's arbitrary inhabited carrier types.
;; Defstubs conservatively expose exactly the selectors used by the VC; the
;; statement predicate below makes nonemptiness and every typing law explicit.

(defstub mp-add-ptr64-p (pointer) t)
(defstub mp-add-zone-p (zone) t)
(defstub mp-add-ptr-data-length (pointer) t)
(defstub mp-add-pelts (pointer index) t)
(defstub mp-add-ptr-offset (pointer) t)
(defstub mp-add-ptr-min (pointer) t)
(defstub mp-add-ptr-max (pointer) t)
(defstub mp-add-ptr-writable (pointer) t)
(defstub mp-add-ptr-zone (pointer) t)

(defun-sk mp-add-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mp-add-ptr64-p pointer)))

(defun-sk mp-add-zone-domain-nonempty-p ()
  (exists (zone)
    (mp-add-zone-p zone)))

(defun-sk mp-add-pointer-selectors-typed-p ()
  (forall (pointer index)
    (implies
     (mp-add-ptr64-p pointer)
     (and
      (natp (mp-add-ptr-data-length pointer))
      (integerp (mp-add-ptr-offset pointer))
      (integerp (mp-add-ptr-min pointer))
      (integerp (mp-add-ptr-max pointer))
      (booleanp (mp-add-ptr-writable pointer))
      (mp-add-zone-p (mp-add-ptr-zone pointer))
      (implies
       (integerp index)
       (mp-add-bv64-p
        (mp-add-pelts pointer index)))))))

(defun mp-add-pointer-interface-p ()
  (and
   (mp-add-pointer-domain-nonempty-p)
   (mp-add-zone-domain-nonempty-p)
   (mp-add-pointer-selectors-typed-p)))

;; Int.toNat is used for source recursion counts and exponents.

(defun mp-add-int-to-nat (value)
  (if (and (integerp value)
           (< value 0))
      0
    (nfix value)))

;; Little-endian radix-2^64 value. The count is Int.toNat(size), matching the
;; source value_sub recursion from offset to offset + size.

(defun mp-add-value-count (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (mp-add-pelts pointer index)
       (* 18446744073709551616
          (mp-add-value-count
           pointer
           (+ 1 index)
           (- count 1))))))

(defun mp-add-value (pointer size)
  (mp-add-value-count
   pointer
   (mp-add-ptr-offset pointer)
   (mp-add-int-to-nat size)))

(defun mp-add-radix-power (exponent)
  (expt
   18446744073709551616
   (mp-add-int-to-nat exponent)))

;; This is C.valid, including the signed-32 size bounds and pointer interval.

(defun mp-add-valid-p (pointer size)
  (and
   (mp-add-ptr64-p pointer)
   (mp-add-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mp-add-ptr-min pointer))
   (<= (mp-add-ptr-min pointer)
       (mp-add-ptr-offset pointer))
   (<= (+ (mp-add-ptr-offset pointer) size)
       (mp-add-ptr-max pointer))
   (<= (mp-add-ptr-max pointer)
       (mp-add-ptr-data-length pointer))))

(defun mp-add-copy-fields-p (new old)
  (and
   (equal (mp-add-ptr-data-length new)
          (mp-add-ptr-data-length old))
   (equal (mp-add-ptr-offset new)
          (mp-add-ptr-offset old))
   (equal (mp-add-ptr-min new)
          (mp-add-ptr-min old))
   (equal (mp-add-ptr-max new)
          (mp-add-ptr-max old))
   (equal (mp-add-ptr-writable new)
          (mp-add-ptr-writable old))
   (equal (mp-add-ptr-zone new)
          (mp-add-ptr-zone old))))

(defun-sk mp-add-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mp-add-ptr-offset new))
       (<= (+ (mp-add-ptr-offset new) size)
           index))
      (equal
       (mp-add-pelts new index)
       (mp-add-pelts old index))))))

(defun-sk mp-add-tail-equal-p
    (new old from size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= from index)
       (< index size))
      (equal
       (mp-add-pelts
        new
        (+ (mp-add-ptr-offset new) index))
       (mp-add-pelts
        old
        (+ (mp-add-ptr-offset new) index)))))))

;; Extensional equality with the single map update appearing in the source.

(defun-sk mp-add-pelts-update-p
    (new old update-index result)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mp-add-pelts new index)
      (if (equal index update-index)
          result
        (mp-add-pelts old index))))))

(defun mp-add-value-equation-p
    (new old-x y size y-size carry)
  (equal
   (+ (mp-add-value new size)
      (* (mp-add-radix-power size)
         carry))
   (+ (mp-add-value old-x size)
      (mp-add-value y y-size))))

(defun mp-add-carry-range-p (carry)
  (and
   (<= 0 carry)
   (<= carry 1)))

;; The following predicates preserve the VC's nested universal continuations
;; from the innermost Boolean equality test outward.

(defun mp-add-o4-body-p
    (sy sx x y i c x3 o3 res o4)
  (implies
   (and
    (implies
     (equal res 0)
     (equal o4 t))
    (implies
     (equal o4 t)
     (equal res 0)))
   (if (not (equal o4 t))
       (and
        (mp-add-value-equation-p
         x3 x y
         (mp-add-signed32 sx)
         (mp-add-signed32 sy)
         0)
        (mp-add-carry-range-p 0)
        (mp-add-outside-equal-p
         x3 x (mp-add-signed32 sx)))
     (and
      (<= 0
          (- (mp-add-signed32 sx)
             (mp-add-signed32 i)))
      (< (- (mp-add-signed32 sx)
            (mp-add-signed32 o3))
         (- (mp-add-signed32 sx)
            (mp-add-signed32 i)))
      (<= (mp-add-signed32 sy)
          (mp-add-signed32 o3))
      (<= (mp-add-signed32 o3)
          (mp-add-signed32 sx))
      (mp-add-value-equation-p
       x3 x y
       (mp-add-signed32 o3)
       (mp-add-signed32 sy)
       c)
      (mp-add-carry-range-p c)
      (or
       (equal o3 sx)
       (equal c 1))
      (mp-add-tail-equal-p
       x3 x
       (mp-add-signed32 o3)
       (mp-add-signed32 sx))
      (mp-add-outside-equal-p
       x3 x (mp-add-signed32 sx))))))

(defun-sk mp-add-all-o4-p
    (sy sx x y i c x3 o3 res)
  (forall (o4)
    (implies
     (booleanp o4)
     (mp-add-o4-body-p
      sy sx x y i c x3 o3 res o4))))

(defun-sk mp-add-all-o3-p
    (sy sx x y i c x3 res)
  (forall (o3)
    (implies
     (mp-add-bv32-p o3)
     (implies
      (equal
       (mp-add-signed32 o3)
       (+ (mp-add-signed32 i) 1))
      (mp-add-all-o4-p
       sy sx x y i c x3 o3 res)))))

(defun mp-add-x3-body-p
    (sy sx x y i c x2 res x3)
  (implies
   (mp-add-copy-fields-p x3 x2)
   (implies
    (and
     (mp-add-pelts-update-p
      x3
      x2
      (+ (mp-add-ptr-offset x3)
         (mp-add-signed32 i))
      res)
     (equal
      (mp-add-pelts
       x3
       (+ (mp-add-ptr-offset x3)
          (mp-add-signed32 i)))
      res))
    (and
     (mp-add-int32-in-bounds-p
      (+ (mp-add-signed32 i) 1))
     (mp-add-all-o3-p
      sy sx x y i c x3 res)))))

(defun-sk mp-add-all-x3-p
    (sy sx x y i c x2 res)
  (forall (x3)
    (implies
     (mp-add-ptr64-p x3)
     (mp-add-x3-body-p
      sy sx x y i c x2 res x3))))

(defun mp-add-res-body-p
    (sy sx x y i c x2 res)
  (implies
   (equal
    res
    (mod
     (+ (mp-add-pelts
         x2
         (+ (mp-add-ptr-offset x2)
            (mp-add-signed32 i)))
        1)
     18446744073709551616))
   (and
    (<= (mp-add-ptr-min x2)
        (+ (mp-add-ptr-offset x2)
           (mp-add-signed32 i)))
    (< (+ (mp-add-ptr-offset x2)
          (mp-add-signed32 i))
       (mp-add-ptr-max x2))
    (equal (mp-add-ptr-writable x2) t)
    (mp-add-all-x3-p
     sy sx x y i c x2 res))))

(defun-sk mp-add-all-res-p
    (sy sx x y i c x2)
  (forall (res)
    (implies
     (mp-add-bv64-p res)
     (mp-add-res-body-p
      sy sx x y i c x2 res))))

(defun mp-add-i-loop-body-p
    (sy sx x y x1 i c x2)
  (implies
   (mp-add-copy-fields-p x2 x1)
   (implies
    (and
     (<= (mp-add-signed32 sy)
         (mp-add-signed32 i))
     (<= (mp-add-signed32 i)
         (mp-add-signed32 sx))
     (mp-add-value-equation-p
      x2 x y
      (mp-add-signed32 i)
      (mp-add-signed32 sy)
      c)
     (mp-add-carry-range-p c)
     (or
      (equal i sx)
      (equal c 1))
     (mp-add-tail-equal-p
      x2 x
      (mp-add-signed32 i)
      (mp-add-signed32 sx))
     (mp-add-outside-equal-p
      x2 x (mp-add-signed32 sx)))
    (if (< (mp-add-signed32 i)
           (mp-add-signed32 sx))
        (and
         (<= (mp-add-ptr-min x2)
             (+ (mp-add-ptr-offset x2)
                (mp-add-signed32 i)))
         (< (+ (mp-add-ptr-offset x2)
               (mp-add-signed32 i))
            (mp-add-ptr-max x2))
         (mp-add-all-res-p
          sy sx x y i c x2))
      (and
       (mp-add-value-equation-p
        x2 x y
        (mp-add-signed32 sx)
        (mp-add-signed32 sy)
        c)
       (mp-add-carry-range-p c)
       (mp-add-outside-equal-p
        x2 x (mp-add-signed32 sx)))))))

(defun-sk mp-add-all-i-loop-p
    (sy sx x y x1)
  (forall (i c x2)
    (implies
     (and
      (mp-add-bv32-p i)
      (mp-add-bv64-p c)
      (mp-add-ptr64-p x2))
     (mp-add-i-loop-body-p
      sy sx x y x1 i c x2))))

(defun mp-add-o2-body-p
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
         (<= (mp-add-signed32 sy)
             (mp-add-signed32 sy))
         (<= (mp-add-signed32 sy)
             (mp-add-signed32 sx)))
        (mp-add-value-equation-p
         x1 x y
         (mp-add-signed32 sy)
         (mp-add-signed32 sy)
         o1)
        (mp-add-carry-range-p o1)
        (or
         (equal sy sx)
         (equal o1 1))
        (mp-add-tail-equal-p
         x1 x
         (mp-add-signed32 sy)
         (mp-add-signed32 sx))
        (mp-add-outside-equal-p
         x1 x (mp-add-signed32 sx))
        (mp-add-all-i-loop-p
         sy sx x y x1))
     (and
      (mp-add-value-equation-p
       x1 x y
       (mp-add-signed32 sx)
       (mp-add-signed32 sy)
       o1)
      (mp-add-carry-range-p o1)
      (mp-add-outside-equal-p
       x1 x (mp-add-signed32 sx))))))

(defun-sk mp-add-all-o2-p
    (sy sx x y x1 o1)
  (forall (o2)
    (implies
     (booleanp o2)
     (mp-add-o2-body-p
      sy sx x y x1 o1 o2))))

(defun mp-add-o1-body-p
    (sy sx x y x1 o1)
  (implies
   (and
    (mp-add-carry-range-p o1)
    (mp-add-value-equation-p
     x1 x y
     (mp-add-signed32 sy)
     (mp-add-signed32 sy)
     o1)
    (mp-add-outside-equal-p
     x1 x (mp-add-signed32 sy)))
   (mp-add-all-o2-p
    sy sx x y x1 o1)))

(defun-sk mp-add-all-o1-p
    (sy sx x y x1)
  (forall (o1)
    (implies
     (mp-add-bv64-p o1)
     (mp-add-o1-body-p
      sy sx x y x1 o1))))

(defun mp-add-x1-body-p
    (sy sx x y x1)
  (implies
   (mp-add-copy-fields-p x1 x)
   (mp-add-all-o1-p
    sy sx x y x1)))

(defun-sk mp-add-all-x1-p
    (sy sx x y)
  (forall (x1)
    (implies
     (mp-add-ptr64-p x1)
     (mp-add-x1-body-p
      sy sx x y x1))))

(defun-sk
    ntp4vc-pearl-multiprecision-add-addold-wmpn-add-in-placeqtvc-statement
    ()
  (forall (sy sx x y)
    (implies
     (and
      (mp-add-pointer-interface-p)
      (mp-add-bv32-p sy)
      (mp-add-bv32-p sx)
      (mp-add-ptr64-p x)
      (mp-add-ptr64-p y)
      (<= 0 (mp-add-signed32 sy))
      (<= (mp-add-signed32 sy)
          (mp-add-signed32 sx))
      (mp-add-valid-p
       x (mp-add-signed32 sx))
      (mp-add-valid-p
       y (mp-add-signed32 sy))
      (equal (mp-add-ptr-writable x) t))
     (and
      (mp-add-valid-p
       x (mp-add-signed32 sy))
      (mp-add-valid-p
       y (mp-add-signed32 sy))
      (equal (mp-add-ptr-writable x) t)
      (mp-add-all-x1-p
       sy sx x y)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
