;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/compare_Compare_wmpn_cmpqtvc: the verification
;; condition for comparing two valid equal-length multiprecision unsigned
;; integers by scanning their 64-bit limbs from most to least significant.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical unsigned representatives are in bijection with fixed-width
;; words. Signed conversion is the exact two's-complement interpretation.

(defun mpcmp-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpcmp-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpcmp-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpcmp-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

(defun mpcmp-bv64-list-p (values)
  (if (consp values)
      (and
       (mpcmp-bv64-p (car values))
       (mpcmp-bv64-list-p (cdr values)))
    (equal values nil)))

;; Pointers and zones remain arbitrary inhabited source carrier types.
;; Conservative stubs expose exactly the pointer observations used by the
;; source theory; every typing condition is explicit in the statement.

(defstub mpcmp-pointer-p (pointer) t)
(defstub mpcmp-zone-p (zone) t)
(defstub mpcmp-data (pointer) t)
(defstub mpcmp-offset (pointer) t)
(defstub mpcmp-minimum (pointer) t)
(defstub mpcmp-maximum (pointer) t)
(defstub mpcmp-writable (pointer) t)
(defstub mpcmp-zone (pointer) t)

(defun-sk mpcmp-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpcmp-pointer-p pointer)))

(defun-sk mpcmp-zone-domain-nonempty-p ()
  (exists (zone)
    (mpcmp-zone-p zone)))

(defun-sk mpcmp-pointer-selectors-typed-p ()
  (forall (pointer)
    (implies
     (mpcmp-pointer-p pointer)
     (and
      (mpcmp-bv64-list-p
       (mpcmp-data pointer))
      (integerp
       (mpcmp-offset pointer))
      (integerp
       (mpcmp-minimum pointer))
      (integerp
       (mpcmp-maximum pointer))
      (booleanp
       (mpcmp-writable pointer))
      (mpcmp-zone-p
       (mpcmp-zone pointer))))))

(defun mpcmp-pointer-interface-p ()
  (and
   (mpcmp-pointer-domain-nonempty-p)
   (mpcmp-zone-domain-nonempty-p)
   (mpcmp-pointer-selectors-typed-p)))

;; This is Int.toNat followed by total list indexing, with zero as the fixed
;; default inhabitant of the 64-bit word type.

(defun mpcmp-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun mpcmp-pelt (pointer index)
  (let* ((natural-index
          (mpcmp-int-to-nat index))
         (value
          (nth natural-index
               (mpcmp-data pointer))))
    (if (mpcmp-bv64-p value)
        value
      0)))

;; Little-endian radix-2^64 value of the indicated pointer prefix.

(defun mpcmp-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpcmp-pelt pointer index)
     (*
      18446744073709551616
      (mpcmp-value-from
       pointer
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpcmp-value (pointer size)
  (mpcmp-value-from
   pointer
   (mpcmp-offset pointer)
   (mpcmp-int-to-nat size)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpcmp-valid-p (pointer size)
  (and
   (mpcmp-pointer-p pointer)
   (mpcmp-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0
       (mpcmp-minimum pointer))
   (<= (mpcmp-minimum pointer)
       (mpcmp-offset pointer))
   (<= (+ (mpcmp-offset pointer)
          size)
       (mpcmp-maximum pointer))
   (<= (mpcmp-maximum pointer)
       (len (mpcmp-data pointer)))))

(defun mpcmp-compare-int (left right)
  (if (< left right)
      -1
    (if (equal left right)
        0
      1)))

;; Equality of the two pointer slices over the source's full integer index
;; domain. Empty intervals remain explicit, as they are in the VC.

(defun-sk mpcmp-tail-equal-p
    (x y lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (mpcmp-pelt
        x
        (+ (mpcmp-offset x)
           index))
       (mpcmp-pelt
        y
        (+ (mpcmp-offset y)
           index)))))))

;; The Boolean continuation says exactly that O2 reflects equality of the two
;; canonical 64-bit limbs, then preserves the VC's unequal/equal branches.

(defun mpcmp-o2-body-p
    (x sz y i o1 o2)
  (let* ((position
          (mpcmp-signed32 o1))
         (loop-index
          (mpcmp-signed32 i))
         (size
          (mpcmp-signed32 sz))
         (lx
          (mpcmp-pelt
           x
           (+ (mpcmp-offset x)
              position)))
         (ly
          (mpcmp-pelt
           y
           (+ (mpcmp-offset y)
              position)))
         (comparison
          (mpcmp-compare-int
           (mpcmp-value x size)
           (mpcmp-value y size))))
    (implies
     (and
      (implies
       (equal lx ly)
       (equal o2 t))
      (implies
       (equal o2 t)
       (equal lx ly)))
     (if (not (equal o2 t))
         (if (< ly lx)
             (equal 1 comparison)
           (equal -1 comparison))
       (and
        (< position loop-index)
        (<= 0 position)
        (<= position size)
        (mpcmp-tail-equal-p
         x y position size))))))

(defun-sk mpcmp-all-o2-p
    (x sz y i o1)
  (forall (o2)
    (implies
     (booleanp o2)
     (mpcmp-o2-body-p
      x sz y i o1 o2))))

(defun mpcmp-o1-body-p
    (x sz y i o1)
  (let ((position
         (mpcmp-signed32 o1)))
    (implies
     (equal
      position
      (- (mpcmp-signed32 i) 1))
     (and
      (<= (mpcmp-minimum x)
          (+ (mpcmp-offset x)
             position))
      (< (+ (mpcmp-offset x)
            position)
         (mpcmp-maximum x))
      (<= (mpcmp-minimum y)
          (+ (mpcmp-offset y)
             position))
      (< (+ (mpcmp-offset y)
            position)
         (mpcmp-maximum y))
      (mpcmp-all-o2-p
       x sz y i o1)))))

(defun-sk mpcmp-all-o1-p
    (x sz y i)
  (forall (o1)
    (implies
     (mpcmp-bv32-p o1)
     (mpcmp-o1-body-p
      x sz y i o1))))

(defun mpcmp-i-body-p
    (x sz y i)
  (let ((loop-index
         (mpcmp-signed32 i))
        (size
         (mpcmp-signed32 sz)))
    (implies
     (and
      (<= 0 loop-index)
      (<= loop-index size)
      (mpcmp-tail-equal-p
       x y loop-index size))
     (if (<= 1 loop-index)
         (and
          (mpcmp-int32-in-bounds-p
           (- loop-index 1))
          (mpcmp-all-o1-p
           x sz y i))
       (equal
        0
        (mpcmp-compare-int
         (mpcmp-value x size)
         (mpcmp-value y size)))))))

(defun-sk mpcmp-all-i-p (x sz y)
  (forall (i)
    (implies
     (mpcmp-bv32-p i)
     (mpcmp-i-body-p
      x sz y i))))

(defun-sk
    ntp4vc-pearl-multiprecision-compare-compare-wmpn-cmpqtvc-statement
    ()
  (forall (x sz y)
    (implies
     (and
      (mpcmp-pointer-interface-p)
      (mpcmp-pointer-p x)
      (mpcmp-bv32-p sz)
      (mpcmp-pointer-p y)
      (mpcmp-valid-p
       x (mpcmp-signed32 sz))
      (mpcmp-valid-p
       y (mpcmp-signed32 sz)))
     (let ((size
            (mpcmp-signed32 sz)))
       (and
        (<= 0 size)
        (<= size size)
        (mpcmp-tail-equal-p
         x y size size)
        (mpcmp-all-i-p
         x sz y))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
