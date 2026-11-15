;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/add_Add_wmpn_addqtvc: the verification condition for
;; unequal-length multi-precision addition, including carry propagation,
;; pointer aliasing, memory framing, and loop continuations. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical unsigned representatives are in bijection with the source
;; fixed-width words. Signed conversion is two's-complement interpretation.

(defun mpwa-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpwa-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpwa-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpwa-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones remain arbitrary inhabited source carrier types.
;; Conservative stubs expose exactly the observations used by the VC; all
;; source typing conditions are explicit in MPWA-POINTER-INTERFACE-P.

(defstub mpwa-pointer-p (pointer) t)
(defstub mpwa-zone-p (zone) t)
(defstub mpwa-data-length (pointer) t)
(defstub mpwa-pelt (pointer index) t)
(defstub mpwa-offset (pointer) t)
(defstub mpwa-minimum (pointer) t)
(defstub mpwa-maximum (pointer) t)
(defstub mpwa-writable (pointer) t)
(defstub mpwa-zone (pointer) t)

(defun-sk mpwa-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpwa-pointer-p pointer)))

(defun-sk mpwa-zone-domain-nonempty-p ()
  (exists (zone)
    (mpwa-zone-p zone)))

(defun-sk mpwa-pointer-selectors-typed-p ()
  (forall (pointer index)
    (implies
     (mpwa-pointer-p pointer)
     (and
      (natp (mpwa-data-length pointer))
      (integerp (mpwa-offset pointer))
      (integerp (mpwa-minimum pointer))
      (integerp (mpwa-maximum pointer))
      (booleanp (mpwa-writable pointer))
      (mpwa-zone-p (mpwa-zone pointer))
      (implies
       (integerp index)
       (mpwa-bv64-p
        (mpwa-pelt pointer index)))))))

(defun mpwa-pointer-interface-p ()
  (and
   (mpwa-pointer-domain-nonempty-p)
   (mpwa-zone-domain-nonempty-p)
   (mpwa-pointer-selectors-typed-p)))

;; Int.toNat is used for source recursion counts and exponents.

(defun mpwa-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

;; Little-endian radix-2^64 value of the indicated pointer prefix.

(defun mpwa-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpwa-pelt pointer index)
     (*
      18446744073709551616
      (mpwa-value-from
       pointer
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpwa-value (pointer size)
  (mpwa-value-from
   pointer
   (mpwa-offset pointer)
   (mpwa-int-to-nat size)))

(defun mpwa-radix-power (exponent)
  (expt
   18446744073709551616
   (mpwa-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpwa-valid-p (pointer size)
  (and
   (mpwa-pointer-p pointer)
   (mpwa-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpwa-minimum pointer))
   (<= (mpwa-minimum pointer)
       (mpwa-offset pointer))
   (<= (+ (mpwa-offset pointer) size)
       (mpwa-maximum pointer))
   (<= (mpwa-maximum pointer)
       (mpwa-data-length pointer))))

(defun mpwa-separated-or-equal-p
    (left right left-size right-size)
  (or
   (equal (mpwa-offset left)
          (mpwa-offset right))
   (<= (+ (mpwa-offset left) left-size)
       (mpwa-offset right))
   (<= (+ (mpwa-offset right) right-size)
       (mpwa-offset left))))

;; Extensional equality, interval equality, and frame preservation range over
;; the full integer index domain of the source maps.

(defun-sk mpwa-same-pelts-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpwa-pelt left index)
      (mpwa-pelt right index)))))

(defun mpwa-same-data-p (left right)
  (and
   (equal
    (mpwa-data-length left)
    (mpwa-data-length right))
   (mpwa-same-pelts-p left right)))

(defun-sk mpwa-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (mpwa-pelt left index)
       (mpwa-pelt right index))))))

(defun-sk mpwa-frame-p (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpwa-offset new))
       (<= (+ (mpwa-offset new) size)
           index))
      (equal
       (mpwa-pelt new index)
       (mpwa-pelt old index))))))

;; Extensional equality with the single map update used by each write.

(defun-sk mpwa-update-p
    (new old update-index value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpwa-pelt new index)
      (if (equal index update-index)
          value
        (mpwa-pelt old index))))))

(defun mpwa-write-relation-p
    (new old update-index value)
  (and
   (mpwa-update-p
    new old update-index value)
   (equal
    (mpwa-pelt new update-index)
    value)))

;; Each mutable-pointer continuation in the source copies the pointer
;; metadata and makes all three new pointers observe one shared array value.

(defun mpwa-snapshot-p
    (new-y new-x new-r old-y old-x old-r)
  (and
   (mpwa-same-data-p new-y new-r)
   (equal (mpwa-data-length new-r)
          (mpwa-data-length old-y))
   (equal (mpwa-offset new-y)
          (mpwa-offset old-y))
   (equal (mpwa-minimum new-y)
          (mpwa-minimum old-y))
   (equal (mpwa-maximum new-y)
          (mpwa-maximum old-y))
   (equal (mpwa-writable new-y)
          (mpwa-writable old-y))
   (equal (mpwa-zone new-y)
          (mpwa-zone old-y))
   (mpwa-same-data-p new-x new-r)
   (equal (mpwa-data-length new-r)
          (mpwa-data-length old-x))
   (equal (mpwa-offset new-x)
          (mpwa-offset old-x))
   (equal (mpwa-minimum new-x)
          (mpwa-minimum old-x))
   (equal (mpwa-maximum new-x)
          (mpwa-maximum old-x))
   (equal (mpwa-writable new-x)
          (mpwa-writable old-x))
   (equal (mpwa-zone new-x)
          (mpwa-zone old-x))
   (equal (mpwa-data-length new-r)
          (mpwa-data-length old-r))
   (equal (mpwa-offset new-r)
          (mpwa-offset old-r))
   (equal (mpwa-minimum new-r)
          (mpwa-minimum old-r))
   (equal (mpwa-maximum new-r)
          (mpwa-maximum old-r))
   (equal (mpwa-writable new-r)
          (mpwa-writable old-r))
   (equal (mpwa-zone new-r)
          (mpwa-zone old-r))))

(defun mpwa-carry-range-p (carry)
  (and
   (<= 0 carry)
   (<= carry 1)))

(defun mpwa-value-equation-p
    (state-r original-x original-y index y-size carry)
  (equal
   (+
    (mpwa-value state-r index)
    (*
     (mpwa-radix-power index)
     carry))
   (+
    (mpwa-value original-x index)
    (mpwa-value original-y y-size))))

(defun mpwa-state-core-p
    (sy sx r x y state-y state-x state-r index carry)
  (let ((short-size (mpwa-signed32 sy))
        (size (mpwa-signed32 sx))
        (position (mpwa-signed32 index)))
    (and
     (<= short-size position)
     (<= position size)
     (mpwa-value-equation-p
      state-r x y position short-size carry)
     (mpwa-frame-p state-r r position)
     (mpwa-same-pelts-p state-x state-r)
     (mpwa-same-pelts-p state-y state-r)
     (or
      (equal (mpwa-offset state-r)
             (mpwa-offset state-x))
      (mpwa-map-eq-sub-p
       state-x x
       (mpwa-offset state-x)
       (+ (mpwa-offset state-x) size)))
     (or
      (equal (mpwa-offset state-r)
             (mpwa-offset state-y))
      (mpwa-map-eq-sub-p
       state-y y
       (mpwa-offset state-y)
       (+ (mpwa-offset state-y)
          short-size)))
     (mpwa-carry-range-p carry))))

(defun mpwa-carry-loop-invariant-p
    (sy sx r x y state-y state-x state-r index carry)
  (and
   (mpwa-state-core-p
    sy sx r x y
    state-y state-x state-r
    index carry)
   (or
    (equal index sx)
    (equal carry 1))))

(defun mpwa-copy-loop-invariant-p
    (sy sx r x y state-y state-x state-r index carry)
  (and
   (mpwa-state-core-p
    sy sx r x y
    state-y state-x state-r
    index carry)
   (or
    (equal index sx)
    (equal carry 0))))

(defun mpwa-final-postcondition-p
    (sy sx r x y state-y state-x state-r carry)
  (let ((short-size (mpwa-signed32 sy))
        (size (mpwa-signed32 sx)))
    (and
     (mpwa-value-equation-p
      state-r x y size short-size carry)
     (mpwa-carry-range-p carry)
     (mpwa-frame-p state-r r size)
     (or
      (equal (mpwa-offset state-r)
             (mpwa-offset state-x))
      (mpwa-map-eq-sub-p
       state-x x
       (mpwa-offset state-x)
       (+ (mpwa-offset state-x) size)))
     (or
      (equal (mpwa-offset state-r)
             (mpwa-offset state-y))
      (mpwa-map-eq-sub-p
       state-y y
       (mpwa-offset state-y)
       (+ (mpwa-offset state-y)
          short-size))))))

(defun mpwa-readable-p (pointer index)
  (and
   (<= (mpwa-minimum pointer)
       (+ (mpwa-offset pointer) index))
   (< (+ (mpwa-offset pointer) index)
      (mpwa-maximum pointer))))

(defun mpwa-writable-at-p (pointer index)
  (and
   (mpwa-readable-p pointer index)
   (equal (mpwa-writable pointer) t)))

;; The second loop copies unchanged high limbs after carry propagation stops.

(defun mpwa-copy-next-index-body-p
    (sy sx r x y i carry
        state-y state-x state-r next-index)
  (implies
   (equal
    (mpwa-signed32 next-index)
    (+ (mpwa-signed32 i) 1))
   (and
    (<= 0
        (- (mpwa-signed32 sx)
           (mpwa-signed32 i)))
    (< (- (mpwa-signed32 sx)
          (mpwa-signed32 next-index))
       (- (mpwa-signed32 sx)
          (mpwa-signed32 i)))
    (mpwa-copy-loop-invariant-p
     sy sx r x y
     state-y state-x state-r
     next-index carry))))

(defun-sk mpwa-all-copy-next-indices-p
    (sy sx r x y i carry
        state-y state-x state-r)
  (forall (next-index)
    (implies
     (mpwa-bv32-p next-index)
     (mpwa-copy-next-index-body-p
      sy sx r x y i carry
      state-y state-x state-r
      next-index))))

(defun mpwa-copy-written-state-body-p
    (sy sx r x y i carry
        old-y old-x old-r
        new-y new-x new-r)
  (implies
   (mpwa-snapshot-p
    new-y new-x new-r
    old-y old-x old-r)
   (implies
    (mpwa-write-relation-p
     new-r
     old-r
     (+ (mpwa-offset new-r)
        (mpwa-signed32 i))
     (mpwa-pelt
      old-x
      (+ (mpwa-offset old-x)
         (mpwa-signed32 i))))
    (and
     (mpwa-int32-in-bounds-p
      (+ (mpwa-signed32 i) 1))
     (mpwa-all-copy-next-indices-p
      sy sx r x y i carry
      new-y new-x new-r)))))

(defun-sk mpwa-all-copy-written-states-p
    (sy sx r x y i carry
        old-y old-x old-r)
  (forall (new-y new-x new-r)
    (implies
     (and
      (mpwa-pointer-p new-y)
      (mpwa-pointer-p new-x)
      (mpwa-pointer-p new-r))
     (mpwa-copy-written-state-body-p
      sy sx r x y i carry
      old-y old-x old-r
      new-y new-x new-r))))

(defun mpwa-copy-loop-step-p
    (sy sx r x y i carry
        state-y state-x state-r)
  (if (< (mpwa-signed32 i)
         (mpwa-signed32 sx))
      (and
       (mpwa-readable-p
        state-x (mpwa-signed32 i))
       (mpwa-readable-p
        x (mpwa-signed32 i))
       (mpwa-writable-at-p
        state-r (mpwa-signed32 i))
       (mpwa-all-copy-written-states-p
        sy sx r x y i carry
        state-y state-x state-r))
    (mpwa-final-postcondition-p
     sy sx r x y
     state-y state-x state-r carry)))

(defun mpwa-copy-loop-state-body-p
    (sy sx r x y carry
        base-y base-x base-r
        i state-y state-x state-r)
  (implies
   (mpwa-snapshot-p
    state-y state-x state-r
    base-y base-x base-r)
   (implies
    (mpwa-copy-loop-invariant-p
     sy sx r x y
     state-y state-x state-r
     i carry)
    (mpwa-copy-loop-step-p
     sy sx r x y i carry
     state-y state-x state-r))))

(defun-sk mpwa-all-copy-loop-states-p
    (sy sx r x y carry
        base-y base-x base-r)
  (forall (i state-y state-x state-r)
    (implies
     (and
      (mpwa-bv32-p i)
      (mpwa-pointer-p state-y)
      (mpwa-pointer-p state-x)
      (mpwa-pointer-p state-r))
     (mpwa-copy-loop-state-body-p
      sy sx r x y carry
      base-y base-x base-r
      i state-y state-x state-r))))

;; The first loop propagates a carry by adding one until a nonzero limb is
;; produced or the end of the long operand is reached.

(defun mpwa-zero-test-body-p
    (sy sx r x y i carry
        state-y state-x state-r
        next-index result zero-test)
  (implies
   (and
    (implies
     (equal result 0)
     (equal zero-test t))
    (implies
     (equal zero-test t)
     (equal result 0)))
   (if (not (equal zero-test t))
       (and
        (mpwa-copy-loop-invariant-p
         sy sx r x y
         state-y state-x state-r
         next-index 0)
        (mpwa-all-copy-loop-states-p
         sy sx r x y 0
         state-y state-x state-r))
     (and
      (<= 0
          (- (mpwa-signed32 sx)
             (mpwa-signed32 i)))
      (< (- (mpwa-signed32 sx)
            (mpwa-signed32 next-index))
         (- (mpwa-signed32 sx)
            (mpwa-signed32 i)))
      (mpwa-carry-loop-invariant-p
       sy sx r x y
       state-y state-x state-r
       next-index carry)))))

(defun-sk mpwa-all-zero-tests-p
    (sy sx r x y i carry
        state-y state-x state-r
        next-index result)
  (forall (zero-test)
    (implies
     (booleanp zero-test)
     (mpwa-zero-test-body-p
      sy sx r x y i carry
      state-y state-x state-r
      next-index result zero-test))))

(defun mpwa-carry-next-index-body-p
    (sy sx r x y i carry
        state-y state-x state-r
        result next-index)
  (implies
   (equal
    (mpwa-signed32 next-index)
    (+ (mpwa-signed32 i) 1))
   (mpwa-all-zero-tests-p
    sy sx r x y i carry
    state-y state-x state-r
    next-index result)))

(defun-sk mpwa-all-carry-next-indices-p
    (sy sx r x y i carry
        state-y state-x state-r result)
  (forall (next-index)
    (implies
     (mpwa-bv32-p next-index)
     (mpwa-carry-next-index-body-p
      sy sx r x y i carry
      state-y state-x state-r
      result next-index))))

(defun mpwa-carry-written-state-body-p
    (sy sx r x y i carry result
        old-y old-x old-r
        new-y new-x new-r)
  (implies
   (mpwa-snapshot-p
    new-y new-x new-r
    old-y old-x old-r)
   (implies
    (mpwa-write-relation-p
     new-r
     old-r
     (+ (mpwa-offset new-r)
        (mpwa-signed32 i))
     result)
    (and
     (mpwa-int32-in-bounds-p
      (+ (mpwa-signed32 i) 1))
     (mpwa-all-carry-next-indices-p
      sy sx r x y i carry
      new-y new-x new-r result)))))

(defun-sk mpwa-all-carry-written-states-p
    (sy sx r x y i carry result
        old-y old-x old-r)
  (forall (new-y new-x new-r)
    (implies
     (and
      (mpwa-pointer-p new-y)
      (mpwa-pointer-p new-x)
      (mpwa-pointer-p new-r))
     (mpwa-carry-written-state-body-p
      sy sx r x y i carry result
      old-y old-x old-r
      new-y new-x new-r))))

(defun mpwa-result-body-p
    (sy sx r x y i carry
        state-y state-x state-r result)
  (implies
   (equal
    result
    (mod
     (+ (mpwa-pelt
         state-x
         (+ (mpwa-offset state-x)
            (mpwa-signed32 i)))
        1)
     18446744073709551616))
   (and
    (mpwa-writable-at-p
     state-r (mpwa-signed32 i))
    (mpwa-all-carry-written-states-p
     sy sx r x y i carry result
     state-y state-x state-r))))

(defun-sk mpwa-all-results-p
    (sy sx r x y i carry
        state-y state-x state-r)
  (forall (result)
    (implies
     (mpwa-bv64-p result)
     (mpwa-result-body-p
      sy sx r x y i carry
      state-y state-x state-r
      result))))

(defun mpwa-carry-loop-step-p
    (sy sx r x y i carry
        state-y state-x state-r)
  (if (< (mpwa-signed32 i)
         (mpwa-signed32 sx))
      (and
       (mpwa-readable-p
        state-x (mpwa-signed32 i))
       (mpwa-readable-p
        x (mpwa-signed32 i))
       (mpwa-all-results-p
        sy sx r x y i carry
        state-y state-x state-r))
    (mpwa-final-postcondition-p
     sy sx r x y
     state-y state-x state-r carry)))

(defun mpwa-carry-loop-state-body-p
    (sy sx r x y
        base-y base-x base-r
        i carry state-y state-x state-r)
  (implies
   (mpwa-snapshot-p
    state-y state-x state-r
    base-y base-x base-r)
   (implies
    (mpwa-carry-loop-invariant-p
     sy sx r x y
     state-y state-x state-r
     i carry)
    (mpwa-carry-loop-step-p
     sy sx r x y i carry
     state-y state-x state-r))))

(defun-sk mpwa-all-carry-loop-states-p
    (sy sx r x y base-y base-x base-r)
  (forall (i carry state-y state-x state-r)
    (implies
     (and
      (mpwa-bv32-p i)
      (mpwa-bv64-p carry)
      (mpwa-pointer-p state-y)
      (mpwa-pointer-p state-x)
      (mpwa-pointer-p state-r))
     (mpwa-carry-loop-state-body-p
      sy sx r x y
      base-y base-x base-r
      i carry state-y state-x state-r))))

;; The result of wmpn_add_n supplies the initial carry and the modified short
;; prefix before the two loops above.

(defun mpwa-initial-result-premise-p
    (sy r x y state-y state-x state-r carry)
  (let ((short-size (mpwa-signed32 sy)))
    (and
     (mpwa-value-equation-p
      state-r x y
      short-size short-size carry)
     (mpwa-carry-range-p carry)
     (mpwa-frame-p state-r r short-size)
     (or
      (equal (mpwa-offset state-r)
             (mpwa-offset state-x))
      (mpwa-map-eq-sub-p
       state-x x
       (mpwa-offset state-x)
       (+ (mpwa-offset state-x)
          short-size)))
     (or
      (equal (mpwa-offset state-r)
             (mpwa-offset state-y))
      (mpwa-map-eq-sub-p
       state-y y
       (mpwa-offset state-y)
       (+ (mpwa-offset state-y)
          short-size))))))

(defun mpwa-initial-zero-test-body-p
    (sy sx r x y
        state-y state-x state-r
        carry zero-test)
  (implies
   (and
    (implies
     (equal carry 0)
     (equal zero-test t))
    (implies
     (equal zero-test t)
     (equal carry 0)))
   (if (not (equal zero-test t))
       (and
        (mpwa-carry-loop-invariant-p
         sy sx r x y
         state-y state-x state-r
         sy carry)
        (mpwa-all-carry-loop-states-p
         sy sx r x y
         state-y state-x state-r))
     (and
      (mpwa-copy-loop-invariant-p
       sy sx r x y
       state-y state-x state-r
       sy carry)
      (mpwa-all-copy-loop-states-p
       sy sx r x y carry
       state-y state-x state-r)))))

(defun-sk mpwa-all-initial-zero-tests-p
    (sy sx r x y
        state-y state-x state-r carry)
  (forall (zero-test)
    (implies
     (booleanp zero-test)
     (mpwa-initial-zero-test-body-p
      sy sx r x y
      state-y state-x state-r
      carry zero-test))))

(defun mpwa-initial-result-body-p
    (sy sx r x y
        state-y state-x state-r carry)
  (implies
   (mpwa-initial-result-premise-p
    sy r x y
    state-y state-x state-r carry)
   (mpwa-all-initial-zero-tests-p
    sy sx r x y
    state-y state-x state-r carry)))

(defun-sk mpwa-all-initial-results-p
    (sy sx r x y state-y state-x state-r)
  (forall (carry)
    (implies
     (mpwa-bv64-p carry)
     (mpwa-initial-result-body-p
      sy sx r x y
      state-y state-x state-r carry))))

(defun mpwa-initial-state-body-p
    (sy sx r x y state-y state-x state-r)
  (implies
   (mpwa-snapshot-p
    state-y state-x state-r
    y x r)
   (mpwa-all-initial-results-p
    sy sx r x y
    state-y state-x state-r)))

(defun-sk mpwa-all-initial-states-p
    (sy sx r x y)
  (forall (state-y state-x state-r)
    (implies
     (and
      (mpwa-pointer-p state-y)
      (mpwa-pointer-p state-x)
      (mpwa-pointer-p state-r))
     (mpwa-initial-state-body-p
      sy sx r x y
      state-y state-x state-r))))

(defun mpwa-conclusion-p (sy sx r x y)
  (let ((short-size (mpwa-signed32 sy)))
    (and
     (<= 0 short-size)
     (mpwa-valid-p r short-size)
     (mpwa-valid-p x short-size)
     (mpwa-valid-p y short-size)
     (mpwa-separated-or-equal-p
      r x short-size short-size)
     (mpwa-separated-or-equal-p
      r y short-size short-size)
     (mpwa-same-data-p r x)
     (mpwa-same-data-p x y)
     (equal (mpwa-writable r) t)
     (mpwa-all-initial-states-p
      sy sx r x y))))

(defun-sk
    ntp4vc-pearl-multiprecision-add-add-wmpn-addqtvc-statement
    ()
  (forall (sy sx r x y)
    (implies
     (and
      (mpwa-pointer-interface-p)
      (mpwa-bv32-p sy)
      (mpwa-bv32-p sx)
      (mpwa-pointer-p r)
      (mpwa-pointer-p x)
      (mpwa-pointer-p y)
      (<= 0 (mpwa-signed32 sy))
      (<= (mpwa-signed32 sy)
          (mpwa-signed32 sx))
      (mpwa-valid-p
       r (mpwa-signed32 sx))
      (mpwa-valid-p
       x (mpwa-signed32 sx))
      (mpwa-valid-p
       y (mpwa-signed32 sy))
      (mpwa-separated-or-equal-p
       r x
       (mpwa-signed32 sx)
       (mpwa-signed32 sx))
      (mpwa-separated-or-equal-p
       r y
       (mpwa-signed32 sx)
       (mpwa-signed32 sy))
      (mpwa-same-data-p r x)
      (mpwa-same-data-p x y)
      (equal (mpwa-writable r) t))
     (mpwa-conclusion-p sy sx r x y))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
