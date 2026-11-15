;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/add_1_Add_1_wmpn_incr_1qtvc: the verification
;; condition for incrementing a nonempty multiprecision value in place,
;; including carry-loop invariants, pointer updates, and memory framing.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source pointers remain abstract.  Their data length and total
;; integer-indexed limb map are independent observations, matching the Why3
;; array model.  All source typing conditions are explicit in
;; MPINCR1-INTERFACE-P.

(defstub mpincr1-ptr-p (x) t)
(defstub mpincr1-zone-p (x) t)
(defstub mpincr1-data-length (x) t)
(defstub mpincr1-pelt (x index) t)
(defstub mpincr1-offset (x) t)
(defstub mpincr1-minimum (x) t)
(defstub mpincr1-maximum (x) t)
(defstub mpincr1-writable (x) t)
(defstub mpincr1-zone (x) t)

(defun mpincr1-uint64-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 18446744073709551616)))

(defun mpincr1-uint32-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 4294967296)))

(defun mpincr1-bool-p (x)
  (or
   (equal x t)
   (equal x nil)))

;; Exact two's-complement signed interpretation of a 32-bit word.

(defun mpincr1-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun mpincr1-int32-in-bounds-p (x)
  (and
   (integerp x)
   (<= -2147483648 x)
   (<= x 2147483647)))

(defun-sk mpincr1-pointer-domain-nonempty-p ()
  (exists (x)
    (mpincr1-ptr-p x)))

(defun-sk mpincr1-interface-typed-p ()
  (forall (x index)
    (implies
     (mpincr1-ptr-p x)
     (and
      (natp (mpincr1-data-length x))
      (integerp (mpincr1-offset x))
      (integerp (mpincr1-minimum x))
      (integerp (mpincr1-maximum x))
      (mpincr1-bool-p
       (mpincr1-writable x))
      (mpincr1-zone-p
       (mpincr1-zone x))
      (implies
       (integerp index)
       (mpincr1-uint64-p
        (mpincr1-pelt x index)))))))

(defun mpincr1-interface-p ()
  (and
   (mpincr1-pointer-domain-nonempty-p)
   (mpincr1-interface-typed-p)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpincr1-valid-p (x size)
  (and
   (mpincr1-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpincr1-minimum x))
   (<= (mpincr1-minimum x)
       (mpincr1-offset x))
   (<= (+ (mpincr1-offset x) size)
       (mpincr1-maximum x))
   (<= (mpincr1-maximum x)
       (mpincr1-data-length x))))

;; Little-endian radix-2^64 value of a prefix beginning at the pointer offset.

(defun mpincr1-value-from (x index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpincr1-pelt x index)
     (*
      18446744073709551616
      (mpincr1-value-from
       x
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpincr1-value (x count)
  (mpincr1-value-from
   x
   (mpincr1-offset x)
   count))

(defun mpincr1-radix-power (exponent)
  (expt 18446744073709551616 (nfix exponent)))

;; Extensional equality of the source pelts maps over their full integer
;; domain.

(defun-sk mpincr1-same-pelts-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpincr1-pelt left index)
      (mpincr1-pelt right index)))))

;; Exact source equality to a single functional update.

(defun-sk mpincr1-single-update-p
    (new old update-index value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpincr1-pelt new index)
      (if (equal index update-index)
          value
        (mpincr1-pelt old index))))))

;; Equality of every pointer observation required after C.incr.

(defun mpincr1-shifted-pointer-p
    (shifted base amount)
  (and
   (equal
    (mpincr1-offset shifted)
    (+ (mpincr1-offset base) amount))
   (equal
    (mpincr1-data-length shifted)
    (mpincr1-data-length base))
   (mpincr1-same-pelts-p shifted base)
   (equal
    (mpincr1-minimum shifted)
    (mpincr1-minimum base))
   (equal
    (mpincr1-maximum shifted)
    (mpincr1-maximum base))
   (equal
    (mpincr1-zone shifted)
    (mpincr1-zone base))
   (equal
    (mpincr1-writable shifted)
    (mpincr1-writable base))))

;; Metadata equalities in the universally quantified loop state.

(defun mpincr1-loop-memory-metadata-p
    (memory old)
  (and
   (equal
    (mpincr1-data-length memory)
    (mpincr1-data-length old))
   (equal
    (mpincr1-offset memory)
    (mpincr1-offset old))
   (equal
    (mpincr1-minimum memory)
    (mpincr1-minimum old))
   (equal
    (mpincr1-maximum memory)
    (mpincr1-maximum old))
   (equal
    (mpincr1-writable memory)
    (mpincr1-writable old))
   (equal
    (mpincr1-zone memory)
    (mpincr1-zone old))))

(defun mpincr1-loop-pointer-p
    (pointer memory index)
  (and
   (equal
    (mpincr1-offset pointer)
    (+ (mpincr1-offset memory) index))
   (mpincr1-same-pelts-p pointer memory)
   (equal
    (mpincr1-data-length pointer)
    (mpincr1-data-length memory))
   (equal
    (mpincr1-minimum pointer)
    (mpincr1-minimum memory))
   (equal
    (mpincr1-maximum pointer)
    (mpincr1-maximum memory))))

;; The memory at indices from START through SIZE-1 is unchanged.

(defun-sk mpincr1-tail-unchanged-p
    (new old start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= start index)
       (< index size))
      (equal
       (mpincr1-pelt
        new
        (+ (mpincr1-offset new)
           index))
       (mpincr1-pelt
        old
        (+ (mpincr1-offset new)
           index)))))))

;; The memory outside [offset(new), offset(new)+size) is unchanged.

(defun-sk mpincr1-frame-p (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpincr1-offset new))
       (<= (+ (mpincr1-offset new) size)
           index))
      (equal
       (mpincr1-pelt new index)
       (mpincr1-pelt old index))))))

(defun mpincr1-initial-invariant-p
    (pointer old size-word)
  (and
   (and
    (<= 0 0)
    (<= 0 (mpincr1-sint32 size-word)))
   (not (equal 0 size-word))
   (equal
    (mpincr1-offset pointer)
    (+ (mpincr1-offset old) 0))
   (mpincr1-same-pelts-p pointer old)
   (equal
    (mpincr1-data-length pointer)
    (mpincr1-data-length old))
   (and
    (equal
     (mpincr1-minimum pointer)
     (mpincr1-minimum old))
    (equal
     (mpincr1-maximum pointer)
     (mpincr1-maximum old)))
   (not (equal 1 0))
   (and
    (<= 0 1)
    (<= 1 1))
   (equal
    (mpincr1-writable pointer)
    t)
   (equal
    (+
     (mpincr1-value old 0)
     (* (mpincr1-radix-power 0) 1))
    (+ (mpincr1-value old 0) 1))))

(defun mpincr1-loop-invariant-p
    (pointer index-word carry result memory old size-word)
  (let ((index (mpincr1-sint32 index-word))
        (size (mpincr1-sint32 size-word)))
    (and
     (and
      (<= 0 index)
      (<= index size))
     (implies
      (equal index-word size-word)
      (not (equal result 0)))
     (mpincr1-loop-pointer-p
      pointer memory index)
     (iff
      (not (equal result 0))
      (equal carry 0))
     (and
      (<= 0 carry)
      (<= carry 1))
     (equal
      (mpincr1-writable pointer)
      t)
     (equal
      (+
       (mpincr1-value memory index)
       (*
        (mpincr1-radix-power index)
        carry))
      (+ (mpincr1-value old index) 1))
     (mpincr1-tail-unchanged-p
      memory old index size)
     (mpincr1-frame-p
      memory old size))))

(defun mpincr1-final-state-p
    (memory old size-word)
  (let ((size (mpincr1-sint32 size-word)))
    (and
     (equal
      (mpincr1-value memory size)
      (+ (mpincr1-value old size) 1))
     (mpincr1-frame-p memory old size))))

;; Metadata conditions around the source C.set operation.

(defun mpincr1-write-metadata-p
    (updated post-write before-write)
  (and
   (mpincr1-same-pelts-p
    updated post-write)
   (equal
    (mpincr1-data-length updated)
    (mpincr1-data-length post-write))
   (equal
    (mpincr1-data-length post-write)
    (mpincr1-data-length before-write))
   (equal
    (mpincr1-offset updated)
    (mpincr1-offset before-write))
   (equal
    (mpincr1-minimum updated)
    (mpincr1-minimum before-write))
   (equal
    (mpincr1-maximum updated)
    (mpincr1-maximum before-write))
   (equal
    (mpincr1-writable updated)
    (mpincr1-writable before-write))
   (equal
    (mpincr1-zone updated)
    (mpincr1-zone before-write))))

(defun mpincr1-post-write-loop-metadata-p
    (post-write memory)
  (and
   (equal
    (mpincr1-data-length post-write)
    (mpincr1-data-length memory))
   (equal
    (mpincr1-offset post-write)
    (mpincr1-offset memory))
   (equal
    (mpincr1-minimum post-write)
    (mpincr1-minimum memory))
   (equal
    (mpincr1-maximum post-write)
    (mpincr1-maximum memory))
   (equal
    (mpincr1-writable post-write)
    (mpincr1-writable memory))
   (equal
    (mpincr1-zone post-write)
    (mpincr1-zone memory))))

(defun mpincr1-next-loop-invariant-p
    (pointer next-index-word carry result memory old index-word size-word)
  (let ((next-index
         (mpincr1-sint32 next-index-word))
        (index
         (mpincr1-sint32 index-word))
        (size
         (mpincr1-sint32 size-word)))
    (and
     (and
      (<= 0 (- size index))
      (< (- size next-index)
         (- size index)))
     (and
      (<= 0 next-index)
      (<= next-index size))
     (implies
      (equal next-index-word size-word)
      (not (equal result 0)))
     (mpincr1-loop-pointer-p
      pointer memory next-index)
     (iff
      (not (equal result 0))
      (equal carry 0))
     (and
      (<= 0 carry)
      (<= carry 1))
     (equal
      (mpincr1-writable pointer)
      t)
     (equal
      (+
       (mpincr1-value memory next-index)
       (*
        (mpincr1-radix-power next-index)
        carry))
      (+ (mpincr1-value old next-index) 1))
     (mpincr1-tail-unchanged-p
      memory old next-index size)
     (mpincr1-frame-p
      memory old size))))

(defun-sk mpincr1-o5-continuation-p
    (updated post-write old index-word next-index-word
             size-word result carry)
  (forall (pointer)
    (implies
     (mpincr1-ptr-p pointer)
     (implies
      (mpincr1-shifted-pointer-p
       pointer updated 1)
      (mpincr1-next-loop-invariant-p
       pointer
       next-index-word
       carry
       result
       post-write
       old
       index-word
       size-word)))))

(defun-sk mpincr1-o4-continuation-p
    (updated post-write old index-word size-word result carry)
  (forall (next-index-word)
    (implies
     (mpincr1-uint32-p next-index-word)
     (implies
      (equal
       (mpincr1-sint32 next-index-word)
       (+ (mpincr1-sint32 index-word) 1))
      (and
       (and
        (<=
         (mpincr1-minimum updated)
         (+ (mpincr1-offset updated) 1))
        (<=
         (+ (mpincr1-offset updated) 1)
         (mpincr1-maximum updated)))
       (mpincr1-o5-continuation-p
        updated
        post-write
        old
        index-word
        next-index-word
        size-word
        result
        carry))))))

(defun-sk mpincr1-write-continuation-p
    (pointer memory old index-word size-word result carry)
  (forall (updated post-write)
    (implies
     (and
      (mpincr1-ptr-p updated)
      (mpincr1-ptr-p post-write))
     (implies
      (mpincr1-write-metadata-p
       updated post-write pointer)
      (implies
       (mpincr1-write-metadata-p
        updated post-write pointer)
       (implies
        (mpincr1-post-write-loop-metadata-p
         post-write memory)
        (implies
         (mpincr1-single-update-p
          updated
          pointer
          (mpincr1-offset updated)
          result)
         (and
          (mpincr1-int32-in-bounds-p
           (+ (mpincr1-sint32 index-word) 1))
          (mpincr1-o4-continuation-p
           updated
           post-write
           old
           index-word
           size-word
           result
           carry)))))))))

(defun mpincr1-after-zero-test-p
    (pointer memory old index-word size-word result carry)
  (and
   (and
    (<= (mpincr1-minimum pointer)
        (mpincr1-offset pointer))
    (< (mpincr1-offset pointer)
       (mpincr1-maximum pointer)))
   (equal
    (mpincr1-writable pointer)
    t)
   (mpincr1-write-continuation-p
    pointer
    memory
    old
    index-word
    size-word
    result
    carry)))

(defun-sk mpincr1-o3-continuation-p
    (pointer memory old index-word size-word result)
  (forall (zero-test)
    (implies
     (mpincr1-bool-p zero-test)
     (implies
      (and
       (implies
        (equal result 0)
        (equal zero-test t))
       (implies
        (equal zero-test t)
        (equal result 0)))
      (if (equal zero-test t)
          (mpincr1-after-zero-test-p
           pointer
           memory
           old
           index-word
           size-word
           result
           1)
        (mpincr1-after-zero-test-p
         pointer
         memory
         old
         index-word
         size-word
         result
         0))))))

(defun-sk mpincr1-result-continuation-p
    (pointer memory old index-word size-word)
  (forall (result)
    (implies
     (mpincr1-uint64-p result)
     (implies
      (equal
       result
       (mod
        (+
         (mpincr1-pelt
          pointer
          (mpincr1-offset pointer))
         1)
        18446744073709551616))
      (mpincr1-o3-continuation-p
       pointer
       memory
       old
       index-word
       size-word
       result)))))

(defun mpincr1-result-zero-branch-p
    (pointer memory old index-word size-word)
  (and
   (and
    (<= (mpincr1-minimum pointer)
        (mpincr1-offset pointer))
    (< (mpincr1-offset pointer)
       (mpincr1-maximum pointer)))
   (mpincr1-result-continuation-p
    pointer
    memory
    old
    index-word
    size-word)))

(defun-sk mpincr1-o2-continuation-p
    (pointer memory old index-word size-word result)
  (forall (zero-test)
    (implies
     (mpincr1-bool-p zero-test)
     (implies
      (and
       (implies
        (equal result 0)
        (equal zero-test t))
       (implies
        (equal zero-test t)
        (equal result 0)))
      (if (equal zero-test t)
          (mpincr1-result-zero-branch-p
           pointer
           memory
           old
           index-word
           size-word)
        (mpincr1-final-state-p
         memory
         old
         size-word))))))

(defun-sk mpincr1-loop-states-p
    (old size-word)
  (forall (pointer index-word carry result memory)
    (implies
     (and
      (mpincr1-ptr-p pointer)
      (mpincr1-uint32-p index-word)
      (mpincr1-uint64-p carry)
      (mpincr1-uint64-p result)
      (mpincr1-ptr-p memory))
     (implies
      (mpincr1-loop-memory-metadata-p
       memory old)
      (implies
       (mpincr1-loop-invariant-p
        pointer
        index-word
        carry
        result
        memory
        old
        size-word)
       (mpincr1-o2-continuation-p
        pointer
        memory
        old
        index-word
        size-word
        result))))))

(defun-sk mpincr1-o1-continuation-p
    (old size-word)
  (forall (pointer)
    (implies
     (mpincr1-ptr-p pointer)
     (implies
      (mpincr1-shifted-pointer-p
       pointer old 0)
      (and
       (mpincr1-initial-invariant-p
        pointer old size-word)
       (mpincr1-loop-states-p
        old size-word))))))

(defun
  ntp4vc-pearl-multiprecision-add-1-add-1-wmpn-incr-1qtvc-statement
  (x size-word)
  (let ((size (mpincr1-sint32 size-word)))
    (implies
     (and
      (mpincr1-interface-p)
      (mpincr1-ptr-p x)
      (mpincr1-uint32-p size-word)
      (mpincr1-valid-p x size)
      (< 0 size)
      (< (+ (mpincr1-value x size) 1)
         (mpincr1-radix-power size))
      (equal
       (mpincr1-writable x)
       t))
     (and
      (<=
       (mpincr1-minimum x)
       (+ (mpincr1-offset x) 0))
      (<=
       (+ (mpincr1-offset x) 0)
       (mpincr1-maximum x))
      (mpincr1-o1-continuation-p
       x size-word)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
