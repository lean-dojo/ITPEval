;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_Sub_wmpn_sub_nqtvc: the loop verification
;; condition for equal-length multiprecision subtraction with pointer
;; aliasing, borrow arithmetic, memory updates, and frame preservation. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented exactly by their canonical unsigned
;; integers, with two's-complement interpretation where the source uses sint.

(defun mpsubwn-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpsubwn-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpsubwn-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpsubwn-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

(defun mpsubwn-bv64-list-p (values)
  (if (consp values)
      (and
       (mpsubwn-bv64-p (car values))
       (mpsubwn-bv64-list-p (cdr values)))
    (equal values nil)))

;; Pointer and zone carriers remain arbitrary inhabited source types.
;; Conservative selectors expose exactly the pointer observations in the VC;
;; all source typing conditions are explicit in MPSUBWN-INTERFACE-P.

(defstub mpsubwn-pointer-p (pointer) t)
(defstub mpsubwn-zone-p (zone) t)
(defstub mpsubwn-data (pointer) t)
(defstub mpsubwn-offset (pointer) t)
(defstub mpsubwn-minimum (pointer) t)
(defstub mpsubwn-maximum (pointer) t)
(defstub mpsubwn-writable (pointer) t)
(defstub mpsubwn-zone (pointer) t)

(defun-sk mpsubwn-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpsubwn-pointer-p pointer)))

(defun-sk mpsubwn-zone-domain-nonempty-p ()
  (exists (zone)
    (mpsubwn-zone-p zone)))

(defun-sk mpsubwn-pointer-interface-typed-p ()
  (forall (pointer)
    (implies
     (mpsubwn-pointer-p pointer)
     (and
      (mpsubwn-bv64-list-p
       (mpsubwn-data pointer))
      (integerp
       (mpsubwn-offset pointer))
      (integerp
       (mpsubwn-minimum pointer))
      (integerp
       (mpsubwn-maximum pointer))
      (booleanp
       (mpsubwn-writable pointer))
      (mpsubwn-zone-p
       (mpsubwn-zone pointer))))))

(defun mpsubwn-interface-p ()
  (and
   (mpsubwn-pointer-domain-nonempty-p)
   (mpsubwn-zone-domain-nonempty-p)
   (mpsubwn-pointer-interface-typed-p)))

;; Int.toNat followed by total list indexing, whose fixed default inhabitant
;; for the 64-bit word type is zero.

(defun mpsubwn-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun mpsubwn-pelt (pointer index)
  (let* ((natural-index
          (mpsubwn-int-to-nat index))
         (value
          (nth natural-index
               (mpsubwn-data pointer))))
    (if (mpsubwn-bv64-p value)
        value
      0)))

;; Little-endian radix-2^64 value of the indicated pointer prefix.

(defun mpsubwn-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpsubwn-pelt pointer index)
     (*
      18446744073709551616
      (mpsubwn-value-from
       pointer
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpsubwn-value (pointer size)
  (mpsubwn-value-from
   pointer
   (mpsubwn-offset pointer)
   (mpsubwn-int-to-nat size)))

(defun mpsubwn-radix-power (exponent)
  (expt
   18446744073709551616
   (mpsubwn-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsubwn-valid-p (pointer size)
  (and
   (mpsubwn-pointer-p pointer)
   (mpsubwn-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0
       (mpsubwn-minimum pointer))
   (<= (mpsubwn-minimum pointer)
       (mpsubwn-offset pointer))
   (<= (+ (mpsubwn-offset pointer)
          size)
       (mpsubwn-maximum pointer))
   (<= (mpsubwn-maximum pointer)
       (len (mpsubwn-data pointer)))))

(defun mpsubwn-result-alias-safe-p
    (result operand size)
  (or
   (equal
    (mpsubwn-offset result)
    (mpsubwn-offset operand))
   (<= (+ (mpsubwn-offset result)
          size)
       (mpsubwn-offset operand))
   (<= (+ (mpsubwn-offset operand)
          size)
       (mpsubwn-offset result))))

;; Equality and interval equality of source map observations range over the
;; complete integer index domain.

(defun-sk mpsubwn-pelts-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsubwn-pelt left index)
      (mpsubwn-pelt right index)))))

(defun-sk mpsubwn-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (mpsubwn-pelt left index)
       (mpsubwn-pelt right index))))))

;; Frame equality outside [offset(new), offset(new)+size).

(defun-sk mpsubwn-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index
          (mpsubwn-offset new))
       (<= (+ (mpsubwn-offset new)
              size)
           index))
      (equal
       (mpsubwn-pelt new index)
       (mpsubwn-pelt old index))))))

;; Extensional equality with the single source map update.

(defun-sk mpsubwn-single-update-p
    (new old update-index value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsubwn-pelt new index)
      (if (equal index update-index)
          value
        (mpsubwn-pelt old index))))))

(defun mpsubwn-write-relation-p
    (new old update-index value)
  (and
   (mpsubwn-single-update-p
    new old update-index value)
   (equal
    (mpsubwn-pelt new update-index)
    value)))

;; Each pointer-copy continuation preserves metadata and makes the three new
;; pointers observe one shared data list, exactly as in the exported VC.

(defun mpsubwn-snapshot-p
    (new-y new-x new-r old-y old-x old-r)
  (and
   (equal
    (mpsubwn-data new-y)
    (mpsubwn-data new-r))
   (equal
    (len (mpsubwn-data new-r))
    (len (mpsubwn-data old-y)))
   (equal
    (mpsubwn-offset new-y)
    (mpsubwn-offset old-y))
   (equal
    (mpsubwn-minimum new-y)
    (mpsubwn-minimum old-y))
   (equal
    (mpsubwn-maximum new-y)
    (mpsubwn-maximum old-y))
   (equal
    (mpsubwn-writable new-y)
    (mpsubwn-writable old-y))
   (equal
    (mpsubwn-zone new-y)
    (mpsubwn-zone old-y))
   (equal
    (mpsubwn-data new-x)
    (mpsubwn-data new-r))
   (equal
    (len (mpsubwn-data new-r))
    (len (mpsubwn-data old-x)))
   (equal
    (mpsubwn-offset new-x)
    (mpsubwn-offset old-x))
   (equal
    (mpsubwn-minimum new-x)
    (mpsubwn-minimum old-x))
   (equal
    (mpsubwn-maximum new-x)
    (mpsubwn-maximum old-x))
   (equal
    (mpsubwn-writable new-x)
    (mpsubwn-writable old-x))
   (equal
    (mpsubwn-zone new-x)
    (mpsubwn-zone old-x))
   (equal
    (len (mpsubwn-data new-r))
    (len (mpsubwn-data old-r)))
   (equal
    (mpsubwn-offset new-r)
    (mpsubwn-offset old-r))
   (equal
    (mpsubwn-minimum new-r)
    (mpsubwn-minimum old-r))
   (equal
    (mpsubwn-maximum new-r)
    (mpsubwn-maximum old-r))
   (equal
    (mpsubwn-writable new-r)
    (mpsubwn-writable old-r))
   (equal
    (mpsubwn-zone new-r)
    (mpsubwn-zone old-r))))

(defun mpsubwn-readable-p (pointer index)
  (and
   (<= (mpsubwn-minimum pointer)
       (+ (mpsubwn-offset pointer)
          index))
   (< (+ (mpsubwn-offset pointer)
         index)
      (mpsubwn-maximum pointer))))

(defun mpsubwn-borrow-range-p (borrow)
  (and
   (<= 0 borrow)
   (<= borrow 1)))

(defun mpsubwn-value-equation-p
    (state-r original-x original-y index borrow)
  (equal
   (-
    (mpsubwn-value state-r index)
    (*
     (mpsubwn-radix-power index)
     borrow))
   (-
    (mpsubwn-value original-x index)
    (mpsubwn-value original-y index))))

(defun mpsubwn-alias-state-p
    (state-r state-x state-y original-x original-y size)
  (and
   (mpsubwn-pelts-equal-p
    state-x state-r)
   (mpsubwn-pelts-equal-p
    state-r state-y)
   (or
    (equal
     (mpsubwn-offset state-r)
     (mpsubwn-offset state-x))
    (mpsubwn-map-eq-sub-p
     state-x
     original-x
     (mpsubwn-offset state-x)
     (+ (mpsubwn-offset state-x)
        size)))
   (or
    (equal
     (mpsubwn-offset state-r)
     (mpsubwn-offset state-y))
    (mpsubwn-map-eq-sub-p
     state-y
     original-y
     (mpsubwn-offset state-y)
     (+ (mpsubwn-offset state-y)
        size)))))

(defun mpsubwn-loop-invariant-p
    (size-word original-r original-x original-y
               state-y state-x state-r index-word borrow)
  (let ((size
         (mpsubwn-signed32 size-word))
        (index
         (mpsubwn-signed32 index-word)))
    (and
     (<= 0 index)
     (<= index size)
     (mpsubwn-value-equation-p
      state-r original-x original-y index borrow)
     (mpsubwn-outside-equal-p
      state-r original-r index)
     (mpsubwn-alias-state-p
      state-r state-x state-y
      original-x original-y size)
     (mpsubwn-borrow-range-p borrow))))

(defun mpsubwn-next-invariant-p
    (size-word original-r original-x original-y
               state-y state-x state-r
               index-word next-index-word borrow)
  (let ((size
         (mpsubwn-signed32 size-word))
        (index
         (mpsubwn-signed32 index-word))
        (next-index
         (mpsubwn-signed32 next-index-word)))
    (and
     (<= 0 (- size index))
     (< (- size next-index)
        (- size index))
     (<= 0 next-index)
     (<= next-index size)
     (mpsubwn-value-equation-p
      state-r original-x original-y next-index borrow)
     (mpsubwn-outside-equal-p
      state-r original-r next-index)
     (mpsubwn-alias-state-p
      state-r state-x state-y
      original-x original-y size)
     (mpsubwn-borrow-range-p borrow))))

(defun-sk mpsubwn-all-next-indices-p
    (size-word original-r original-x original-y
               state-y state-x state-r
               index-word borrow)
  (forall (next-index-word)
    (implies
     (mpsubwn-bv32-p next-index-word)
     (implies
      (equal
       (mpsubwn-signed32 next-index-word)
       (+ (mpsubwn-signed32 index-word) 1))
      (mpsubwn-next-invariant-p
       size-word
       original-r original-x original-y
       state-y state-x state-r
       index-word next-index-word borrow)))))

(defun mpsubwn-updated-state-body-p
    (size-word original-r original-x original-y
               old-y old-x old-r
               index-word result borrow
               new-y new-x new-r)
  (implies
   (mpsubwn-snapshot-p
    new-y new-x new-r
    old-y old-x old-r)
   (implies
    (mpsubwn-write-relation-p
     new-r
     old-r
     (+ (mpsubwn-offset new-r)
        (mpsubwn-signed32 index-word))
     result)
    (and
     (mpsubwn-int32-in-bounds-p
      (+ (mpsubwn-signed32 index-word) 1))
     (mpsubwn-all-next-indices-p
      size-word
      original-r original-x original-y
      new-y new-x new-r
      index-word borrow)))))

(defun-sk mpsubwn-all-updated-states-p
    (size-word original-r original-x original-y
               old-y old-x old-r
               index-word result borrow)
  (forall (new-y new-x new-r)
    (implies
     (and
      (mpsubwn-pointer-p new-y)
      (mpsubwn-pointer-p new-x)
      (mpsubwn-pointer-p new-r))
     (mpsubwn-updated-state-body-p
      size-word
      original-r original-x original-y
      old-y old-x old-r
      index-word result borrow
      new-y new-x new-r))))

(defun mpsubwn-sub-with-borrow-p
    (state-x state-y index-word incoming result borrow)
  (let ((index
         (mpsubwn-signed32 index-word)))
    (and
     (equal
      (-
       result
       (* 18446744073709551616 borrow))
      (-
       (-
        (mpsubwn-pelt
         state-x
         (+ (mpsubwn-offset state-x)
            index))
        (mpsubwn-pelt
         state-y
         (+ (mpsubwn-offset state-y)
            index)))
       incoming))
     (mpsubwn-borrow-range-p borrow))))

(defun mpsubwn-result-borrow-body-p
    (size-word original-r original-x original-y
               state-y state-x state-r
               index-word incoming result borrow)
  (implies
   (mpsubwn-sub-with-borrow-p
    state-x state-y
    index-word incoming result borrow)
   (and
    (mpsubwn-readable-p
     state-r
     (mpsubwn-signed32 index-word))
    (equal
     (mpsubwn-writable state-r)
     t)
    (mpsubwn-all-updated-states-p
     size-word
     original-r original-x original-y
     state-y state-x state-r
     index-word result borrow))))

(defun-sk mpsubwn-all-result-borrow-p
    (size-word original-r original-x original-y
               state-y state-x state-r
               index-word incoming)
  (forall (result borrow)
    (implies
     (and
      (mpsubwn-bv64-p result)
      (mpsubwn-bv64-p borrow))
     (mpsubwn-result-borrow-body-p
      size-word
      original-r original-x original-y
      state-y state-x state-r
      index-word incoming result borrow))))

(defun mpsubwn-loop-branch-p
    (size-word original-r original-x original-y
               state-y state-x state-r index-word borrow)
  (let ((size
         (mpsubwn-signed32 size-word))
        (index
         (mpsubwn-signed32 index-word)))
    (if (< index size)
        (and
         (mpsubwn-readable-p state-x index)
         (mpsubwn-readable-p state-y index)
         (mpsubwn-readable-p original-x index)
         (mpsubwn-readable-p original-y index)
         (mpsubwn-borrow-range-p borrow)
         (mpsubwn-all-result-borrow-p
          size-word
          original-r original-x original-y
          state-y state-x state-r
          index-word borrow))
      (and
       (mpsubwn-value-equation-p
        state-r original-x original-y size borrow)
       (mpsubwn-borrow-range-p borrow)
       (mpsubwn-outside-equal-p
        state-r original-r size)
       (or
        (equal
         (mpsubwn-offset state-r)
         (mpsubwn-offset state-x))
        (mpsubwn-map-eq-sub-p
         state-x
         original-x
         (mpsubwn-offset state-x)
         (+ (mpsubwn-offset state-x)
            size)))
       (or
        (equal
         (mpsubwn-offset state-r)
         (mpsubwn-offset state-y))
        (mpsubwn-map-eq-sub-p
         state-y
         original-y
         (mpsubwn-offset state-y)
         (+ (mpsubwn-offset state-y)
            size)))))))

(defun mpsubwn-loop-state-body-p
    (size-word original-r original-x original-y
               index-word borrow state-y state-x state-r)
  (implies
   (mpsubwn-snapshot-p
    state-y state-x state-r
    original-y original-x original-r)
   (implies
    (mpsubwn-loop-invariant-p
     size-word
     original-r original-x original-y
     state-y state-x state-r
     index-word borrow)
    (mpsubwn-loop-branch-p
     size-word
     original-r original-x original-y
     state-y state-x state-r
     index-word borrow))))

(defun-sk mpsubwn-all-loop-states-p
    (size-word original-r original-x original-y)
  (forall (index-word borrow state-y state-x state-r)
    (implies
     (and
      (mpsubwn-bv32-p index-word)
      (mpsubwn-bv64-p borrow)
      (mpsubwn-pointer-p state-y)
      (mpsubwn-pointer-p state-x)
      (mpsubwn-pointer-p state-r))
     (mpsubwn-loop-state-body-p
      size-word
      original-r original-x original-y
      index-word borrow state-y state-x state-r))))

(defun mpsubwn-initial-conclusion-p
    (size-word r x y)
  (let ((size
         (mpsubwn-signed32 size-word)))
    (and
     (<= 0 0)
     (<= 0 size)
     (mpsubwn-value-equation-p
      r x y 0 0)
     (mpsubwn-pelts-equal-p x r)
     (mpsubwn-pelts-equal-p r y)
     (or
      (equal
       (mpsubwn-offset r)
       (mpsubwn-offset x))
      (mpsubwn-map-eq-sub-p
       x x
       (mpsubwn-offset x)
       (+ (mpsubwn-offset x)
          size)))
     (or
      (equal
       (mpsubwn-offset r)
       (mpsubwn-offset y))
      (mpsubwn-map-eq-sub-p
       y y
       (mpsubwn-offset y)
       (+ (mpsubwn-offset y)
          size)))
     (<= 0 0)
     (<= 0 1)
     (mpsubwn-all-loop-states-p
      size-word r x y))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-sub-wmpn-sub-nqtvc-statement
    ()
  (forall (size-word r x y)
    (implies
     (and
      (mpsubwn-interface-p)
      (mpsubwn-bv32-p size-word)
      (mpsubwn-pointer-p r)
      (mpsubwn-pointer-p x)
      (mpsubwn-pointer-p y)
      (<= 0
          (mpsubwn-signed32 size-word))
      (mpsubwn-valid-p
       r
       (mpsubwn-signed32 size-word))
      (mpsubwn-valid-p
       x
       (mpsubwn-signed32 size-word))
      (mpsubwn-valid-p
       y
       (mpsubwn-signed32 size-word))
      (mpsubwn-result-alias-safe-p
       r x
       (mpsubwn-signed32 size-word))
      (mpsubwn-result-alias-safe-p
       r y
       (mpsubwn-signed32 size-word))
      (equal
       (mpsubwn-data r)
       (mpsubwn-data x))
      (equal
       (mpsubwn-data x)
       (mpsubwn-data y))
      (equal
       (mpsubwn-writable r)
       t))
     (mpsubwn-initial-conclusion-p
      size-word r x y))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
