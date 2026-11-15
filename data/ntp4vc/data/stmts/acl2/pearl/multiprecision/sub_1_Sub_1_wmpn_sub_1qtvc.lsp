;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1qtvc: the verification condition
;; for subtracting one 64-bit limb into a multiprecision output,
;; including borrow propagation, copy-loop invariants, and memory framing.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source pointers remain abstract. Their data length is an independent
;; natural-number observation, and their limbs form a total integer-indexed
;; map of 64-bit values. All source typing conditions are explicit in
;; MPSUB1O-INTERFACE-P.

(defstub mpsub1o-ptr-p (x) t)
(defstub mpsub1o-zone-p (x) t)
(defstub mpsub1o-data-length (x) t)
(defstub mpsub1o-pelt (x index) t)
(defstub mpsub1o-offset (x) t)
(defstub mpsub1o-minimum (x) t)
(defstub mpsub1o-maximum (x) t)
(defstub mpsub1o-writable (x) t)
(defstub mpsub1o-zone (x) t)

(defun mpsub1o-uint64-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 18446744073709551616)))

(defun mpsub1o-uint32-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 4294967296)))

(defun mpsub1o-bool-p (x)
  (or
   (equal x t)
   (equal x nil)))

;; Exact two's-complement signed interpretation of a 32-bit word.

(defun mpsub1o-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun mpsub1o-int32-in-bounds-p (x)
  (and
   (integerp x)
   (<= -2147483648 x)
   (<= x 2147483647)))

(defun-sk mpsub1o-pointer-domain-nonempty-p ()
  (exists (x)
    (mpsub1o-ptr-p x)))

(defun-sk mpsub1o-interface-typed-p ()
  (forall (x index)
    (implies
     (mpsub1o-ptr-p x)
     (and
      (natp (mpsub1o-data-length x))
      (integerp (mpsub1o-offset x))
      (integerp (mpsub1o-minimum x))
      (integerp (mpsub1o-maximum x))
      (mpsub1o-bool-p
       (mpsub1o-writable x))
      (mpsub1o-zone-p
       (mpsub1o-zone x))
      (implies
       (integerp index)
       (mpsub1o-uint64-p
        (mpsub1o-pelt x index)))))))

(defun mpsub1o-interface-p ()
  (and
   (mpsub1o-pointer-domain-nonempty-p)
   (mpsub1o-interface-typed-p)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsub1o-valid-p (x size)
  (and
   (mpsub1o-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpsub1o-minimum x))
   (<= (mpsub1o-minimum x)
       (mpsub1o-offset x))
   (<= (+ (mpsub1o-offset x) size)
       (mpsub1o-maximum x))
   (<= (mpsub1o-maximum x)
       (mpsub1o-data-length x))))

;; Little-endian radix-2^64 value of a prefix beginning at the pointer offset.

(defun mpsub1o-value-from (x index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpsub1o-pelt x index)
     (*
      18446744073709551616
      (mpsub1o-value-from
       x
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpsub1o-value (x count)
  (mpsub1o-value-from
   x
   (mpsub1o-offset x)
   count))

(defun mpsub1o-radix-power (exponent)
  (expt 18446744073709551616
        (nfix exponent)))

(defun mpsub1o-pointer-index-valid-p (x index)
  (and
   (<= (mpsub1o-minimum x) index)
   (< index (mpsub1o-maximum x))))

;; Metadata equalities carried by the source pointer-update quantifiers.

(defun mpsub1o-same-metadata-p (new old)
  (and
   (equal
    (mpsub1o-data-length new)
    (mpsub1o-data-length old))
   (equal
    (mpsub1o-offset new)
    (mpsub1o-offset old))
   (equal
    (mpsub1o-minimum new)
    (mpsub1o-minimum old))
   (equal
    (mpsub1o-maximum new)
    (mpsub1o-maximum old))
   (equal
    (mpsub1o-writable new)
    (mpsub1o-writable old))
   (equal
    (mpsub1o-zone new)
    (mpsub1o-zone old))))

;; Exact source equality to a single functional update on the full integer
;; index domain.

(defun-sk mpsub1o-single-update-p
    (new old update-index value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsub1o-pelt new index)
      (if (equal index update-index)
          value
        (mpsub1o-pelt old index))))))

;; The memory outside [offset(new), offset(new)+size) is unchanged from the
;; original output pointer.

(defun-sk mpsub1o-frame-p (new original size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpsub1o-offset new))
       (<= (+ (mpsub1o-offset new) size)
           index))
      (equal
       (mpsub1o-pelt new index)
       (mpsub1o-pelt original index))))))

;; Invariant and terminal condition for the second loop, which copies
;; remaining input limbs once the borrow has become zero.

(defun mpsub1o-copy-invariant-p
    (memory input original-output index-word borrow size-word subtrahend)
  (let ((index (mpsub1o-sint32 index-word))
        (size (mpsub1o-sint32 size-word)))
    (and
     (or
      (equal index-word size-word)
      (equal borrow 0))
     (<= 0 index)
     (<= index size)
     (equal
      (-
       (mpsub1o-value memory index)
       (*
        (mpsub1o-radix-power index)
        borrow))
      (-
       (mpsub1o-value input index)
       subtrahend))
     (mpsub1o-frame-p
      memory original-output size))))

(defun mpsub1o-copy-final-state-p
    (memory input original-output size-word subtrahend borrow)
  (let ((size (mpsub1o-sint32 size-word)))
    (and
     (equal
      (-
       (mpsub1o-value memory size)
       (*
        (mpsub1o-radix-power size)
        borrow))
      (-
       (mpsub1o-value input size)
       subtrahend))
     (mpsub1o-frame-p
      memory original-output size)
     (<= 0 borrow)
     (<= borrow 1))))

(defun-sk mpsub1o-copy-next-index-continuation-p
    (memory input original-output index-word borrow size-word subtrahend)
  (forall (next-index-word)
    (implies
     (mpsub1o-uint32-p next-index-word)
     (implies
      (equal
       (mpsub1o-sint32 next-index-word)
       (+ (mpsub1o-sint32 index-word) 1))
      (and
       (<= 0
           (- (mpsub1o-sint32 size-word)
              (mpsub1o-sint32 index-word)))
       (< (- (mpsub1o-sint32 size-word)
             (mpsub1o-sint32 next-index-word))
          (- (mpsub1o-sint32 size-word)
             (mpsub1o-sint32 index-word)))
       (mpsub1o-copy-invariant-p
        memory
        input
        original-output
        next-index-word
        borrow
        size-word
        subtrahend))))))

(defun-sk mpsub1o-copy-write-continuation-p
    (memory input original-output index-word borrow size-word subtrahend)
  (forall (new-memory)
    (implies
     (mpsub1o-ptr-p new-memory)
     (implies
      (mpsub1o-same-metadata-p
       new-memory memory)
      (implies
       (and
        (mpsub1o-single-update-p
         new-memory
         memory
         (+ (mpsub1o-offset new-memory)
            (mpsub1o-sint32 index-word))
         (mpsub1o-pelt
          input
          (+ (mpsub1o-offset input)
             (mpsub1o-sint32 index-word))))
        (equal
         (mpsub1o-pelt
          new-memory
          (+ (mpsub1o-offset new-memory)
             (mpsub1o-sint32 index-word)))
         (mpsub1o-pelt
          input
          (+ (mpsub1o-offset input)
             (mpsub1o-sint32 index-word)))))
       (and
        (mpsub1o-int32-in-bounds-p
         (+ (mpsub1o-sint32 index-word) 1))
        (mpsub1o-copy-next-index-continuation-p
         new-memory
         input
         original-output
         index-word
         borrow
         size-word
         subtrahend)))))))

(defun mpsub1o-copy-state-continuation-p
    (memory input original-output index-word borrow size-word subtrahend)
  (let ((index (mpsub1o-sint32 index-word))
        (size (mpsub1o-sint32 size-word)))
    (if (< index size)
        (and
         (mpsub1o-pointer-index-valid-p
          input
          (+ (mpsub1o-offset input) index))
         (mpsub1o-pointer-index-valid-p
          memory
          (+ (mpsub1o-offset memory) index))
         (equal
          (mpsub1o-writable memory)
          t)
         (mpsub1o-copy-write-continuation-p
          memory
          input
          original-output
          index-word
          borrow
          size-word
          subtrahend))
      (mpsub1o-copy-final-state-p
       memory
       input
       original-output
       size-word
       subtrahend
       borrow))))

(defun-sk mpsub1o-copy-loop-states-p
    (initial-memory input original-output size-word subtrahend borrow)
  (forall (index-word memory)
    (implies
     (and
      (mpsub1o-uint32-p index-word)
      (mpsub1o-ptr-p memory))
     (implies
      (mpsub1o-same-metadata-p
       memory initial-memory)
      (implies
       (mpsub1o-copy-invariant-p
        memory
        input
        original-output
        index-word
        borrow
        size-word
        subtrahend)
       (mpsub1o-copy-state-continuation-p
        memory
        input
        original-output
        index-word
        borrow
        size-word
        subtrahend))))))

(defun mpsub1o-copy-package-p
    (memory input original-output index-word borrow size-word subtrahend)
  (and
   (mpsub1o-copy-invariant-p
    memory
    input
    original-output
    index-word
    borrow
    size-word
    subtrahend)
   (mpsub1o-copy-loop-states-p
    memory
    input
    original-output
    size-word
    subtrahend
    borrow)))

;; Invariant and continuations for the first loop, which propagates a borrow
;; while input limbs are zero.

(defun mpsub1o-borrow-invariant-p
    (memory input original-output index-word borrow size-word subtrahend)
  (let ((index (mpsub1o-sint32 index-word))
        (size (mpsub1o-sint32 size-word)))
    (and
     (<= 1 index)
     (<= index size)
     (<= 0 borrow)
     (<= borrow 1)
     (or
      (equal index-word size-word)
      (equal borrow 1))
     (equal
      (-
       (mpsub1o-value memory index)
       (*
        (mpsub1o-radix-power index)
        borrow))
      (-
       (mpsub1o-value input index)
       subtrahend))
     (mpsub1o-frame-p
      memory original-output size))))

(defun-sk mpsub1o-borrow-zero-test-continuation-p
    (memory input original-output index-word next-index-word
            borrow size-word subtrahend)
  (forall (zero-test)
    (implies
     (mpsub1o-bool-p zero-test)
     (implies
      (and
       (implies
        (equal
         (mpsub1o-pelt
          input
          (+ (mpsub1o-offset input)
             (mpsub1o-sint32 index-word)))
         0)
        (equal zero-test t))
       (implies
        (equal zero-test t)
        (equal
         (mpsub1o-pelt
          input
          (+ (mpsub1o-offset input)
             (mpsub1o-sint32 index-word)))
         0)))
      (if (not (equal zero-test t))
          (mpsub1o-copy-package-p
           memory
           input
           original-output
           next-index-word
           0
           size-word
           subtrahend)
        (and
         (<= 0
             (- (mpsub1o-sint32 size-word)
                (mpsub1o-sint32 index-word)))
         (< (- (mpsub1o-sint32 size-word)
               (mpsub1o-sint32 next-index-word))
            (- (mpsub1o-sint32 size-word)
               (mpsub1o-sint32 index-word)))
         (mpsub1o-borrow-invariant-p
          memory
          input
          original-output
          next-index-word
          borrow
          size-word
          subtrahend)))))))

(defun-sk mpsub1o-borrow-next-index-continuation-p
    (memory input original-output index-word borrow size-word subtrahend)
  (forall (next-index-word)
    (implies
     (mpsub1o-uint32-p next-index-word)
     (implies
      (equal
       (mpsub1o-sint32 next-index-word)
       (+ (mpsub1o-sint32 index-word) 1))
      (mpsub1o-borrow-zero-test-continuation-p
       memory
       input
       original-output
       index-word
       next-index-word
       borrow
       size-word
       subtrahend)))))

(defun-sk mpsub1o-borrow-write-continuation-p
    (memory input original-output index-word borrow size-word
            subtrahend result)
  (forall (new-memory)
    (implies
     (mpsub1o-ptr-p new-memory)
     (implies
      (mpsub1o-same-metadata-p
       new-memory memory)
      (implies
       (and
        (mpsub1o-single-update-p
         new-memory
         memory
         (+ (mpsub1o-offset new-memory)
            (mpsub1o-sint32 index-word))
         result)
        (equal
         (mpsub1o-pelt
          new-memory
          (+ (mpsub1o-offset new-memory)
             (mpsub1o-sint32 index-word)))
         result))
       (and
        (mpsub1o-int32-in-bounds-p
         (+ (mpsub1o-sint32 index-word) 1))
        (mpsub1o-borrow-next-index-continuation-p
         new-memory
         input
         original-output
         index-word
         borrow
         size-word
         subtrahend)))))))

(defun-sk mpsub1o-borrow-result-continuation-p
    (memory input original-output index-word borrow size-word subtrahend)
  (forall (result)
    (implies
     (mpsub1o-uint64-p result)
     (implies
      (equal
       result
       (mod
        (-
         (mpsub1o-pelt
          input
          (+ (mpsub1o-offset input)
             (mpsub1o-sint32 index-word)))
         1)
        18446744073709551616))
      (and
       (mpsub1o-pointer-index-valid-p
        memory
        (+ (mpsub1o-offset memory)
           (mpsub1o-sint32 index-word)))
       (equal
        (mpsub1o-writable memory)
        t)
       (mpsub1o-borrow-write-continuation-p
        memory
        input
        original-output
        index-word
        borrow
        size-word
        subtrahend
        result))))))

(defun mpsub1o-borrow-state-continuation-p
    (memory input original-output index-word borrow size-word subtrahend)
  (if (< (mpsub1o-sint32 index-word)
         (mpsub1o-sint32 size-word))
      (and
       (mpsub1o-pointer-index-valid-p
        input
        (+ (mpsub1o-offset input)
           (mpsub1o-sint32 index-word)))
       (mpsub1o-borrow-result-continuation-p
        memory
        input
        original-output
        index-word
        borrow
        size-word
        subtrahend))
    (mpsub1o-copy-package-p
     memory
     input
     original-output
     index-word
     borrow
     size-word
     subtrahend)))

(defun-sk mpsub1o-borrow-loop-states-p
    (initial-memory input original-output size-word subtrahend)
  (forall (index-word borrow memory)
    (implies
     (and
      (mpsub1o-uint32-p index-word)
      (mpsub1o-uint64-p borrow)
      (mpsub1o-ptr-p memory))
     (implies
      (mpsub1o-same-metadata-p
       memory initial-memory)
      (implies
       (mpsub1o-borrow-invariant-p
        memory
        input
        original-output
        index-word
        borrow
        size-word
        subtrahend)
       (mpsub1o-borrow-state-continuation-p
        memory
        input
        original-output
        index-word
        borrow
        size-word
        subtrahend))))))

(defun mpsub1o-initial-borrow-package-p
    (memory input original-output size-word subtrahend)
  (and
   (mpsub1o-borrow-invariant-p
    memory
    input
    original-output
    1
    1
    size-word
    subtrahend)
   (mpsub1o-borrow-loop-states-p
    memory
    input
    original-output
    size-word
    subtrahend)))

;; Continuations after the first subtraction and first output write.

(defun mpsub1o-after-first-write-p
    (memory input original-output size-word subtrahend first-limb)
  (if (< first-limb subtrahend)
      (mpsub1o-initial-borrow-package-p
       memory
       input
       original-output
       size-word
       subtrahend)
    (mpsub1o-copy-package-p
     memory
     input
     original-output
     1
     0
     size-word
     subtrahend)))

(defun-sk mpsub1o-first-write-continuation-p
    (input original-output size-word subtrahend first-limb result)
  (forall (memory)
    (implies
     (mpsub1o-ptr-p memory)
     (implies
      (mpsub1o-same-metadata-p
       memory original-output)
      (implies
       (mpsub1o-single-update-p
        memory
        original-output
        (mpsub1o-offset memory)
        result)
       (mpsub1o-after-first-write-p
        memory
        input
        original-output
        size-word
        subtrahend
        first-limb))))))

(defun-sk mpsub1o-first-result-continuation-p
    (input original-output size-word subtrahend first-limb)
  (forall (result)
    (implies
     (mpsub1o-uint64-p result)
     (implies
      (equal
       result
       (mod
        (- first-limb subtrahend)
        18446744073709551616))
      (and
       (mpsub1o-pointer-index-valid-p
        original-output
        (mpsub1o-offset original-output))
       (equal
        (mpsub1o-writable original-output)
        t)
       (mpsub1o-first-write-continuation-p
        input
        original-output
        size-word
        subtrahend
        first-limb
        result))))))

(defun
  ntp4vc-pearl-multiprecision-sub-1-sub-1-wmpn-sub-1qtvc-statement
  (input size-word output subtrahend)
  (let ((size (mpsub1o-sint32 size-word))
        (first-limb
         (mpsub1o-pelt
          input
          (mpsub1o-offset input))))
    (implies
     (and
      (mpsub1o-interface-p)
      (mpsub1o-ptr-p input)
      (mpsub1o-uint32-p size-word)
      (mpsub1o-ptr-p output)
      (mpsub1o-uint64-p subtrahend)
      (mpsub1o-valid-p input size)
      (mpsub1o-valid-p output size)
      (< 0 size)
      (equal
       (mpsub1o-writable output)
       t))
     (and
      (mpsub1o-pointer-index-valid-p
       input
       (mpsub1o-offset input))
      (mpsub1o-first-result-continuation-p
       input
       output
       size-word
       subtrahend
       first-limb)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
