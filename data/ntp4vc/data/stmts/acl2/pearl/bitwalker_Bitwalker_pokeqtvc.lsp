;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitwalker_Bitwalker_pokeqtvc: the bitwalker poke verification
;; condition for writing a bounded sequence of bits from a 64-bit word into
;; a byte stream while preserving the surrounding bits. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Bounded natural representatives are in bijection with the source unsigned
;; fixed-width words. These operations are the corresponding 32-bit modular
;; word operations.

(defun bp-bv8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun bp-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun bp-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun bp-bv32-add (left right)
  (mod (+ left right) 4294967296))

(defun bp-bv32-sub (left right)
  (mod (- left right) 4294967296))

;; A proper list of 8-bit representatives is exactly a source byte stream.

(defun bp-byte-list-p (stream)
  (if (endp stream)
      (equal stream nil)
    (and
     (bp-bv8-p (car stream))
     (bp-byte-list-p (cdr stream)))))

;; Int.toNat maps negative integers to zero. Source list lookup returns the
;; inhabited default byte zero outside the list.

(defun bp-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun bp-nth-byte (stream index)
  (let ((byte (nth (bp-int-to-nat index) stream)))
    (if (bp-bv8-p byte) byte 0)))

;; With positive divisor 8, ACL2 floor/mod are the Euclidean quotient and
;; remainder used by all three source representations.

(defun bp-nth8-stream (stream position)
  (logbitp
   (bp-int-to-nat (- 7 (mod position 8)))
   (bp-nth-byte stream (floor position 8))))

(defun bp-bit64 (word index)
  (logbitp (bp-int-to-nat index) word))

;; This is the unsigned representative of the 64-bit word obtained by shifting
;; one left by the zero-extended 32-bit length.

(defun bp-maxvalue (len)
  (if (< (nfix len) 64)
      (ash 1 (nfix len))
    0))

;; Zero extension preserves unsigned representatives, and 128-bit addition
;; cannot wrap on two 32-bit inputs.

(defun bp-overflow-disjunction-p (left right)
  (or
   (< (+ left right) 4294967296)
   (<= (+ left right) 4294967295)))

;; The byte stream contains the selected bits of value on
;; [start, start + count).

(defun-sk bp-written-prefix-p
    (stream value start len count)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= start index)
       (< index (+ start count)))
      (equal
       (bp-nth8-stream stream index)
       (bp-bit64
        value
        (+ (- (- len index) 1) start)))))))

;; The prefix before start is unchanged.

(defun-sk bp-prefix-unchanged-p
    (original updated start)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index start))
      (equal
       (bp-nth8-stream original index)
       (bp-nth8-stream updated index))))))

;; The suffix beginning at start + count is unchanged through the end of the
;; updated byte stream.

(defun-sk bp-suffix-unchanged-p
    (original updated start count)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= (+ start count) index)
       (< index (* 8 (len updated))))
      (equal
       (bp-nth8-stream updated index)
       (bp-nth8-stream original index))))))

;; The prospective stream differs from the current stream at no in-range bit
;; other than the selected write position.

(defun-sk bp-equal-except-p
    (next current excluded)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (* 8 (len next))))
      (implies
       (not (equal index excluded))
       (equal
        (bp-nth8-stream next index)
        (bp-nth8-stream current index)))))))

;; Preserve the source universal quantification over every updated byte stream
;; of the same length after a single-bit write.

(defun-sk bp-after-write-p
    (original current value start len lstart i)
  (forall (next)
    (implies
     (bp-byte-list-p next)
     (implies
      (equal (len next) (len current))
      (let*
          ((start-plus-i (bp-bv32-add start i))
           (lstart-plus-i (bp-bv32-add lstart i))
           (target (- 63 lstart-plus-i))
           (i-plus-one (bp-bv32-add i 1)))
        (implies
         (and
          (bp-equal-except-p next current start-plus-i)
          (equal
           (bp-nth8-stream next start-plus-i)
           (bp-bit64 value target)))
         (and
          (bp-overflow-disjunction-p i 1)
          (implies
           (equal i-plus-one (+ i 1))
           (and
            (and
             (<= 0 (- len i))
             (< (- len i-plus-one) (- len i)))
            (and
             (<= 0 i-plus-one)
             (<= i-plus-one len))
            (bp-prefix-unchanged-p
             original next start)
            (bp-written-prefix-p
             next value start len i-plus-one)
            (bp-suffix-unchanged-p
             original next start i-plus-one))))))))))

;; Direct encoding of the loop continuation at one source-typed index and
;; current byte stream.

(defun bp-loop-step-p
    (original current value start len lstart i)
  (if (< i len)
      (and
       (bp-overflow-disjunction-p lstart i)
       (implies
        (equal
         (bp-bv32-add lstart i)
         (+ lstart i))
        (and
         (< (bp-bv32-add lstart i) 64)
         (bp-overflow-disjunction-p start i)
         (implies
          (equal
           (bp-bv32-add start i)
           (+ start i))
          (and
           (and
            (< (* 8 (len current)) 4294967296)
            (<
             (bp-bv32-add start i)
             (* 8 (len current))))
           (bp-after-write-p
            original current value start len lstart i))))))
    (and
     (and
      (<= -2 0)
      (<= 0 0))
     (iff
      (equal 0 -1)
      (< (* 8 (len current)) (+ start len)))
     (iff
      (equal 0 -2)
      (and
       (<= (bp-maxvalue len) value)
       (<= (+ start len) (* 8 (len current)))))
     (and
      (< value (bp-maxvalue len))
      (<= (+ start len) (* 8 (len current))))
     (bp-prefix-unchanged-p original current start)
     (bp-written-prefix-p current value start len len)
     (bp-suffix-unchanged-p original current start len))))

;; Preserve the source universal quantifiers over every 32-bit loop index and
;; every equal-length byte stream satisfying the displayed loop invariant.

(defun-sk bp-loop-continuation-p
    (original value start len lstart)
  (forall (i current)
    (implies
     (and
      (bp-bv32-p i)
      (bp-byte-list-p current))
     (implies
      (equal (len current) (len original))
      (implies
       (and
        (and
         (<= 0 i)
         (<= i len))
        (bp-prefix-unchanged-p original current start)
        (bp-written-prefix-p current value start len i)
        (bp-suffix-unchanged-p original current start i))
       (bp-loop-step-p
        original current value start len lstart i))))))

;; Direct encoding of the three result branches following the initial modular
;; addition check.

(defun bp-result-branches-p (len start addr value)
  (let ((start-plus-len (bp-bv32-add start len)))
    (if (< (* 8 (len addr)) start-plus-len)
        (and
         (and
          (<= -2 -1)
          (<= -1 0))
         (< (* 8 (len addr)) (+ start len))
         (iff
          (equal -1 -2)
          (and
           (<= (bp-maxvalue len) value)
           (<= (+ start len) (* 8 (len addr)))))
         (iff
          (equal -1 0)
          (and
           (< value (bp-maxvalue len))
           (<= (+ start len) (* 8 (len addr)))))
         (implies
          (equal -1 0)
          (bp-written-prefix-p
           addr value start len len)))
      (if (<= (bp-maxvalue len) value)
          (and
           (and
            (<= -2 -2)
            (<= -2 0))
           (iff
            (equal -2 -1)
            (< (* 8 (len addr)) (+ start len)))
           (and
            (<= (bp-maxvalue len) value)
            (<= (+ start len) (* 8 (len addr))))
           (iff
            (equal -2 0)
            (and
             (< value (bp-maxvalue len))
             (<= (+ start len) (* 8 (len addr)))))
           (implies
            (equal -2 0)
            (bp-written-prefix-p
             addr value start len len)))
        (and
         (or
          (<= len 64)
          (<= len 64))
         (let ((lstart (bp-bv32-sub 64 len)))
           (implies
            (equal lstart (- 64 len))
            (and
             (and
              (and
               (<= 0 0)
               (<= 0 len))
              (bp-written-prefix-p
               addr value start len 0))
             (bp-loop-continuation-p
              addr value start len lstart)))))))))

(defun
    ntp4vc-pearl-bitwalker-bitwalker-pokeqtvc-statement
    (len start addr value)
  (implies
   (and
    (bp-bv32-p len)
    (bp-bv32-p start)
    (bp-byte-list-p addr)
    (bp-bv64-p value)
    (< len 64)
    (< (+ start len) 4294967296)
    (< (* 8 (len addr)) 4294967296))
   (and
    (bp-overflow-disjunction-p start len)
    (implies
     (equal
      (bp-bv32-add start len)
      (+ start len))
     (bp-result-branches-p len start addr value)))))

(value-triple :itpeval-statement-checked)
:q
