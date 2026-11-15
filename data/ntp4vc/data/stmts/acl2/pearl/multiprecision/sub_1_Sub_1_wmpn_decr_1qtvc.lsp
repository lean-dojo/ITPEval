;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_1_Sub_1_wmpn_decr_1qtvc: the verification
;; condition for decrementing a nonempty multiprecision value in place,
;; including borrow-loop invariants, pointer updates, and memory framing.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source pointers remain abstract, while their data fields are represented
;; exactly as finite lists of 64-bit limbs.  All source typing conditions are
;; explicit in MPDECR1-INTERFACE-P.

(defstub mpdecr1-ptr-p (x) t)
(defstub mpdecr1-zone-p (x) t)
(defstub mpdecr1-data (x) t)
(defstub mpdecr1-offset (x) t)
(defstub mpdecr1-minimum (x) t)
(defstub mpdecr1-maximum (x) t)
(defstub mpdecr1-writable (x) t)
(defstub mpdecr1-zone (x) t)

(defun mpdecr1-uint64-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 18446744073709551616)))

(defun mpdecr1-uint32-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 4294967296)))

(defun mpdecr1-bool-p (x)
  (or
   (equal x t)
   (equal x nil)))

(defun mpdecr1-uint64-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and
     (mpdecr1-uint64-p (car xs))
     (mpdecr1-uint64-list-p (cdr xs)))))

;; Exact two's-complement signed interpretation of a 32-bit word.

(defun mpdecr1-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun mpdecr1-int32-in-bounds-p (x)
  (and
   (integerp x)
   (<= -2147483648 x)
   (<= x 2147483647)))

(defun-sk mpdecr1-pointer-domain-nonempty-p ()
  (exists (x)
    (mpdecr1-ptr-p x)))

(defun-sk mpdecr1-interface-typed-p ()
  (forall (x)
    (implies
     (mpdecr1-ptr-p x)
     (and
      (mpdecr1-uint64-list-p
       (mpdecr1-data x))
      (integerp (mpdecr1-offset x))
      (integerp (mpdecr1-minimum x))
      (integerp (mpdecr1-maximum x))
      (mpdecr1-bool-p
       (mpdecr1-writable x))
      (mpdecr1-zone-p
       (mpdecr1-zone x))))))

(defun mpdecr1-interface-p ()
  (and
   (mpdecr1-pointer-domain-nonempty-p)
   (mpdecr1-interface-typed-p)))

(defun mpdecr1-data-length (x)
  (len (mpdecr1-data x)))

;; The source pelts function uses Int.toNat and a zero default for an index
;; outside the finite data list.

(defun mpdecr1-pelt (x index)
  (let ((value
         (nth
          (nfix index)
          (mpdecr1-data x))))
    (if (mpdecr1-uint64-p value)
        value
      0)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpdecr1-valid-p (x size)
  (and
   (mpdecr1-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpdecr1-minimum x))
   (<= (mpdecr1-minimum x)
       (mpdecr1-offset x))
   (<= (+ (mpdecr1-offset x) size)
       (mpdecr1-maximum x))
   (<= (mpdecr1-maximum x)
       (mpdecr1-data-length x))))

;; Little-endian radix-2^64 value of a prefix beginning at the pointer offset.

(defun mpdecr1-value-from (x index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpdecr1-pelt x index)
     (*
      18446744073709551616
      (mpdecr1-value-from
       x
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpdecr1-value (x count)
  (mpdecr1-value-from
   x
   (mpdecr1-offset x)
   count))

(defun mpdecr1-radix-power (exponent)
  (expt 18446744073709551616 (nfix exponent)))

;; Extensional equality of the source pelts maps over their full integer
;; domain.

(defun-sk mpdecr1-same-pelts-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpdecr1-pelt left index)
      (mpdecr1-pelt right index)))))

;; Exact source equality to a single functional update.

(defun-sk mpdecr1-single-update-p
    (new old update-index value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpdecr1-pelt new index)
      (if (equal index update-index)
          value
        (mpdecr1-pelt old index))))))

;; Equality of every pointer observation required after C.incr.

(defun mpdecr1-shifted-pointer-p
    (shifted base amount)
  (and
   (equal
    (mpdecr1-offset shifted)
    (+ (mpdecr1-offset base) amount))
   (equal
    (mpdecr1-data-length shifted)
    (mpdecr1-data-length base))
   (mpdecr1-same-pelts-p shifted base)
   (equal
    (mpdecr1-data shifted)
    (mpdecr1-data base))
   (equal
    (mpdecr1-minimum shifted)
    (mpdecr1-minimum base))
   (equal
    (mpdecr1-maximum shifted)
    (mpdecr1-maximum base))
   (equal
    (mpdecr1-zone shifted)
    (mpdecr1-zone base))
   (equal
    (mpdecr1-writable shifted)
    (mpdecr1-writable base))))

;; Metadata equalities in the universally quantified loop state.

(defun mpdecr1-loop-memory-metadata-p
    (memory old)
  (and
   (equal
    (mpdecr1-data-length memory)
    (mpdecr1-data-length old))
   (equal
    (mpdecr1-offset memory)
    (mpdecr1-offset old))
   (equal
    (mpdecr1-minimum memory)
    (mpdecr1-minimum old))
   (equal
    (mpdecr1-maximum memory)
    (mpdecr1-maximum old))
   (equal
    (mpdecr1-writable memory)
    (mpdecr1-writable old))
   (equal
    (mpdecr1-zone memory)
    (mpdecr1-zone old))))

(defun mpdecr1-loop-pointer-p
    (pointer memory index)
  (and
   (equal
    (mpdecr1-offset pointer)
    (+ (mpdecr1-offset memory) index))
   (mpdecr1-same-pelts-p pointer memory)
   (equal
    (mpdecr1-data-length pointer)
    (mpdecr1-data-length memory))
   (equal
    (mpdecr1-minimum pointer)
    (mpdecr1-minimum memory))
   (equal
    (mpdecr1-maximum pointer)
    (mpdecr1-maximum memory))))

;; The memory at indices from START through SIZE-1 is unchanged.

(defun-sk mpdecr1-tail-unchanged-p
    (new old start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= start index)
       (< index size))
      (equal
       (mpdecr1-pelt
        new
        (+ (mpdecr1-offset new)
           index))
       (mpdecr1-pelt
        old
        (+ (mpdecr1-offset new)
           index)))))))

;; The memory outside [offset(new), offset(new)+size) is unchanged.

(defun-sk mpdecr1-frame-p (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpdecr1-offset new))
       (<= (+ (mpdecr1-offset new) size)
           index))
      (equal
       (mpdecr1-pelt new index)
       (mpdecr1-pelt old index))))))

(defun mpdecr1-initial-invariant-p
    (pointer old size-word)
  (and
   (and
    (<= 0 0)
    (<= 0 (mpdecr1-sint32 size-word)))
   (not (equal 0 size-word))
   (equal
    (mpdecr1-offset pointer)
    (+ (mpdecr1-offset old) 0))
   (mpdecr1-same-pelts-p pointer old)
   (equal
    (mpdecr1-data-length pointer)
    (mpdecr1-data-length old))
   (and
    (equal
     (mpdecr1-minimum pointer)
     (mpdecr1-minimum old))
    (equal
     (mpdecr1-maximum pointer)
     (mpdecr1-maximum old)))
   (not (equal 1 0))
   (and
    (<= 0 1)
    (<= 1 1))
   (equal
    (mpdecr1-writable pointer)
    t)
   (equal
    (-
     (mpdecr1-value old 0)
     (* (mpdecr1-radix-power 0) 1))
    (- (mpdecr1-value old 0) 1))))

(defun mpdecr1-loop-invariant-p
    (pointer index-word carry result memory old size-word)
  (let ((index (mpdecr1-sint32 index-word))
        (size (mpdecr1-sint32 size-word)))
    (and
     (and
      (<= 0 index)
      (<= index size))
     (implies
      (equal index-word size-word)
      (not (equal result 0)))
     (mpdecr1-loop-pointer-p
      pointer memory index)
     (iff
      (not (equal result 0))
      (equal carry 0))
     (and
      (<= 0 carry)
      (<= carry 1))
     (equal
      (mpdecr1-writable pointer)
      t)
     (equal
      (-
       (mpdecr1-value memory index)
       (*
        (mpdecr1-radix-power index)
        carry))
      (- (mpdecr1-value old index) 1))
     (mpdecr1-tail-unchanged-p
      memory old index size)
     (mpdecr1-frame-p
      memory old size))))

(defun mpdecr1-final-state-p
    (memory old size-word)
  (let ((size (mpdecr1-sint32 size-word)))
    (and
     (equal
      (mpdecr1-value memory size)
      (- (mpdecr1-value old size) 1))
     (mpdecr1-frame-p memory old size))))

;; Metadata conditions around the source C.set operation.

(defun mpdecr1-write-metadata-p
    (updated post-write before-write)
  (and
   (equal
    (mpdecr1-data updated)
    (mpdecr1-data post-write))
   (equal
    (mpdecr1-data-length post-write)
    (mpdecr1-data-length before-write))
   (equal
    (mpdecr1-offset updated)
    (mpdecr1-offset before-write))
   (equal
    (mpdecr1-minimum updated)
    (mpdecr1-minimum before-write))
   (equal
    (mpdecr1-maximum updated)
    (mpdecr1-maximum before-write))
   (equal
    (mpdecr1-writable updated)
    (mpdecr1-writable before-write))
   (equal
    (mpdecr1-zone updated)
    (mpdecr1-zone before-write))))

(defun mpdecr1-post-write-loop-metadata-p
    (post-write memory)
  (and
   (equal
    (mpdecr1-data-length post-write)
    (mpdecr1-data-length memory))
   (equal
    (mpdecr1-offset post-write)
    (mpdecr1-offset memory))
   (equal
    (mpdecr1-minimum post-write)
    (mpdecr1-minimum memory))
   (equal
    (mpdecr1-maximum post-write)
    (mpdecr1-maximum memory))
   (equal
    (mpdecr1-writable post-write)
    (mpdecr1-writable memory))
   (equal
    (mpdecr1-zone post-write)
    (mpdecr1-zone memory))))

(defun mpdecr1-next-loop-invariant-p
    (pointer next-index-word carry result memory old index-word size-word)
  (let ((next-index
         (mpdecr1-sint32 next-index-word))
        (index
         (mpdecr1-sint32 index-word))
        (size
         (mpdecr1-sint32 size-word)))
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
     (mpdecr1-loop-pointer-p
      pointer memory next-index)
     (iff
      (not (equal result 0))
      (equal carry 0))
     (and
      (<= 0 carry)
      (<= carry 1))
     (equal
      (mpdecr1-writable pointer)
      t)
     (equal
      (-
       (mpdecr1-value memory next-index)
       (*
        (mpdecr1-radix-power next-index)
        carry))
      (- (mpdecr1-value old next-index) 1))
     (mpdecr1-tail-unchanged-p
      memory old next-index size)
     (mpdecr1-frame-p
      memory old size))))

(defun-sk mpdecr1-o5-continuation-p
    (updated post-write old index-word next-index-word
             size-word result carry)
  (forall (pointer)
    (implies
     (mpdecr1-ptr-p pointer)
     (implies
      (mpdecr1-shifted-pointer-p
       pointer updated 1)
      (mpdecr1-next-loop-invariant-p
       pointer
       next-index-word
       carry
       result
       post-write
       old
       index-word
       size-word)))))

(defun-sk mpdecr1-o4-continuation-p
    (updated post-write old index-word size-word result carry)
  (forall (next-index-word)
    (implies
     (mpdecr1-uint32-p next-index-word)
     (implies
      (equal
       (mpdecr1-sint32 next-index-word)
       (+ (mpdecr1-sint32 index-word) 1))
      (and
       (and
        (<=
         (mpdecr1-minimum updated)
         (+ (mpdecr1-offset updated) 1))
        (<=
         (+ (mpdecr1-offset updated) 1)
         (mpdecr1-maximum updated)))
       (mpdecr1-o5-continuation-p
        updated
        post-write
        old
        index-word
        next-index-word
        size-word
        result
        carry))))))

(defun-sk mpdecr1-write-continuation-p
    (pointer memory old index-word size-word result limb carry)
  (forall (updated post-write)
    (implies
     (and
      (mpdecr1-ptr-p updated)
      (mpdecr1-ptr-p post-write))
     (implies
      (mpdecr1-write-metadata-p
       updated post-write pointer)
      (implies
       (mpdecr1-write-metadata-p
        updated post-write pointer)
       (implies
        (mpdecr1-post-write-loop-metadata-p
         post-write memory)
        (implies
         (mpdecr1-single-update-p
          updated
          pointer
          (mpdecr1-offset updated)
          result)
         (and
          (mpdecr1-int32-in-bounds-p
           (+ (mpdecr1-sint32 index-word) 1))
          (mpdecr1-o4-continuation-p
           updated
           post-write
           old
           index-word
           size-word
           limb
           carry)))))))))

(defun mpdecr1-after-zero-test-p
    (pointer memory old index-word size-word result limb carry)
  (and
   (and
    (<= (mpdecr1-minimum pointer)
        (mpdecr1-offset pointer))
    (< (mpdecr1-offset pointer)
       (mpdecr1-maximum pointer)))
   (equal
    (mpdecr1-writable pointer)
    t)
   (mpdecr1-write-continuation-p
    pointer
    memory
    old
    index-word
    size-word
    result
    limb
    carry)))

(defun-sk mpdecr1-o3-continuation-p
    (pointer memory old index-word size-word result)
  (forall (zero-test)
    (implies
     (mpdecr1-bool-p zero-test)
     (implies
      (and
       (implies
        (equal
         (mpdecr1-pelt
          pointer
          (mpdecr1-offset pointer))
         0)
        (equal zero-test t))
       (implies
        (equal zero-test t)
        (equal
         (mpdecr1-pelt
          pointer
          (mpdecr1-offset pointer))
         0)))
      (if (equal zero-test t)
          (mpdecr1-after-zero-test-p
           pointer
           memory
           old
           index-word
           size-word
           result
           (mpdecr1-pelt
            pointer
            (mpdecr1-offset pointer))
           1)
        (mpdecr1-after-zero-test-p
         pointer
         memory
         old
         index-word
         size-word
         result
         (mpdecr1-pelt
          pointer
          (mpdecr1-offset pointer))
         0))))))

(defun-sk mpdecr1-result-continuation-p
    (pointer memory old index-word size-word)
  (forall (result)
    (implies
     (mpdecr1-uint64-p result)
     (implies
      (equal
       result
       (mod
        (-
         (mpdecr1-pelt
          pointer
          (mpdecr1-offset pointer))
         1)
        18446744073709551616))
      (mpdecr1-o3-continuation-p
       pointer
       memory
       old
       index-word
       size-word
       result)))))

(defun mpdecr1-result-zero-branch-p
    (pointer memory old index-word size-word)
  (and
   (and
    (<= (mpdecr1-minimum pointer)
        (mpdecr1-offset pointer))
    (< (mpdecr1-offset pointer)
       (mpdecr1-maximum pointer)))
   (mpdecr1-result-continuation-p
    pointer
    memory
    old
    index-word
    size-word)))

(defun-sk mpdecr1-o2-continuation-p
    (pointer memory old index-word size-word result)
  (forall (zero-test)
    (implies
     (mpdecr1-bool-p zero-test)
     (implies
      (and
       (implies
        (equal result 0)
        (equal zero-test t))
       (implies
        (equal zero-test t)
        (equal result 0)))
      (if (equal zero-test t)
          (mpdecr1-result-zero-branch-p
           pointer
           memory
           old
           index-word
           size-word)
        (mpdecr1-final-state-p
         memory
         old
         size-word))))))

(defun-sk mpdecr1-loop-states-p
    (old size-word)
  (forall (pointer index-word carry result memory)
    (implies
     (and
      (mpdecr1-ptr-p pointer)
      (mpdecr1-uint32-p index-word)
      (mpdecr1-uint64-p carry)
      (mpdecr1-uint64-p result)
      (mpdecr1-ptr-p memory))
     (implies
      (mpdecr1-loop-memory-metadata-p
       memory old)
      (implies
       (mpdecr1-loop-invariant-p
        pointer
        index-word
        carry
        result
        memory
        old
        size-word)
       (mpdecr1-o2-continuation-p
        pointer
        memory
        old
        index-word
        size-word
        result))))))

(defun-sk mpdecr1-o1-continuation-p
    (old size-word)
  (forall (pointer)
    (implies
     (mpdecr1-ptr-p pointer)
     (implies
      (mpdecr1-shifted-pointer-p
       pointer old 0)
      (and
       (mpdecr1-initial-invariant-p
        pointer old size-word)
       (mpdecr1-loop-states-p
        old size-word))))))

(defun
  ntp4vc-pearl-multiprecision-sub-1-sub-1-wmpn-decr-1qtvc-statement
  (x size-word)
  (let ((size (mpdecr1-sint32 size-word)))
    (implies
     (and
      (mpdecr1-interface-p)
      (mpdecr1-ptr-p x)
      (mpdecr1-uint32-p size-word)
      (mpdecr1-valid-p x size)
      (< 0 size)
      (<= 0 (- (mpdecr1-value x size) 1))
      (equal
       (mpdecr1-writable x)
       t))
     (and
      (<=
       (mpdecr1-minimum x)
       (+ (mpdecr1-offset x) 0))
      (<=
       (+ (mpdecr1-offset x) 0)
       (mpdecr1-maximum x))
      (mpdecr1-o1-continuation-p
       x size-word)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
