;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitwalker_Bitwalker_pokethenpeekqtvc: the bitwalker verification
;; condition that writing a bounded run of bits from a 64-bit word into a byte
;; stream and then reading that run returns the original word. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Bounded natural representatives are in bijection with the source unsigned
;; fixed-width words.

(defun ppp-bv8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun ppp-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ppp-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; A proper list of 8-bit representatives is exactly a source byte stream.

(defun ppp-byte-list-p (stream)
  (if (consp stream)
      (and
       (ppp-bv8-p (car stream))
       (ppp-byte-list-p (cdr stream)))
    (equal stream nil)))

;; Int.toNat maps negative integers to zero. Source list lookup returns the
;; inhabited default byte zero outside the list.

(defun ppp-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ppp-nth-byte (stream index)
  (let ((byte (nth (ppp-int-to-nat index) stream)))
    (if (ppp-bv8-p byte) byte 0)))

;; For positive divisor 8, floor and mod are the Euclidean quotient and
;; remainder used by all three ground-truth representations.

(defun ppp-nth8-stream (stream position)
  (logbitp
   (ppp-int-to-nat (- 7 (mod position 8)))
   (ppp-nth-byte stream (floor position 8))))

(defun ppp-bit64 (word index)
  (logbitp (ppp-int-to-nat index) word))

;; This is the unsigned representative of the 64-bit word obtained by shifting
;; one left by the zero-extended 32-bit length.

(defun ppp-maxvalue (len)
  (if (< (nfix len) 64)
      (ash 1 (nfix len))
    0))

;; The prefix preceding the written interval is unchanged.

(defun-sk ppp-prefix-unchanged-p (addr addr1 start)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i start))
      (equal
       (ppp-nth8-stream addr i)
       (ppp-nth8-stream addr1 i))))))

;; The selected interval of addr1 contains the corresponding bits of value.

(defun-sk ppp-written-interval-p (addr1 value start len)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= start i)
       (< i (+ start len)))
      (equal
       (ppp-nth8-stream addr1 i)
       (ppp-bit64
        value
        (+ (- (- len i) 1) start)))))))

;; The suffix following the written interval is unchanged.

(defun-sk ppp-suffix-unchanged-p (addr addr1 start len)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= (+ start len) i)
       (< i (* 8 (len addr1))))
      (equal
       (ppp-nth8-stream addr1 i)
       (ppp-nth8-stream addr i))))))

(defun ppp-successful-write-p (addr addr1 value start len)
  (and
   (ppp-prefix-unchanged-p addr addr1 start)
   (ppp-written-interval-p addr1 value start len)
   (ppp-suffix-unchanged-p addr addr1 start len)))

;; Direct encoding of the antecedent governing each integer poke return code.

(defun ppp-poke-result-description-p
    (poke-result addr addr1 value start len)
  (and
   (<= -2 poke-result)
   (<= poke-result 0)
   (iff
    (equal poke-result -1)
    (< (* 8 (len addr1)) (+ start len)))
   (iff
    (equal poke-result -2)
    (and
     (<= (ppp-maxvalue len) value)
     (<= (+ start len) (* 8 (len addr1)))))
   (iff
    (equal poke-result 0)
    (and
     (< value (ppp-maxvalue len))
     (<= (+ start len) (* 8 (len addr1)))))
   (implies
    (equal poke-result 0)
    (ppp-successful-write-p addr addr1 value start len))))

;; The low len bits of a peek result are the selected stream bits in reverse
;; address order.

(defun-sk ppp-peek-low-bits-p (peek-result addr1 start len)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i len))
      (equal
       (ppp-bit64 peek-result i)
       (ppp-nth8-stream
        addr1
        (- (- (+ start len) i) 1)))))))

;; Every remaining bit of the 64-bit peek result is false.

(defun-sk ppp-peek-high-bits-zero-p (peek-result len)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= len i)
       (< i 64))
      (equal (ppp-bit64 peek-result i) nil)))))

;; This is exactly the conjunction assumed about each source-typed peek result.

(defun ppp-peek-result-description-p
    (peek-result addr1 start len)
  (and
   (implies
    (< (* 8 (len addr1)) (+ start len))
    (equal peek-result 0))
   (implies
    (<= (+ start len) (* 8 (len addr1)))
    (and
     (ppp-peek-low-bits-p peek-result addr1 start len)
     (ppp-peek-high-bits-zero-p peek-result len)))))

;; Preserve the source quantification over every unsigned 64-bit peek result.

(defun-sk ppp-all-peek-results-p (addr1 value start len)
  (forall (peek-result)
    (implies
     (ppp-bv64-p peek-result)
     (implies
      (ppp-peek-result-description-p
       peek-result addr1 start len)
      (equal peek-result value)))))

(defun ppp-poke-postcondition-p (addr1 value start len)
  (and
   (<= len 64)
   (< (+ start len) 4294967296)
   (< (* 8 (len addr1)) 4294967296)
   (ppp-all-peek-results-p addr1 value start len)))

;; Preserve the source quantification over every mathematical integer poke
;; result satisfying the displayed return-code and write postconditions.

(defun-sk ppp-all-poke-results-p (addr addr1 value start len)
  (forall (poke-result)
    (implies
     (integerp poke-result)
     (implies
      (ppp-poke-result-description-p
       poke-result addr addr1 value start len)
      (ppp-poke-postcondition-p addr1 value start len)))))

;; Preserve the source quantification over every equal-length updated byte
;; stream.

(defun-sk ppp-all-updated-streams-p (addr value start len)
  (forall (addr1)
    (implies
     (ppp-byte-list-p addr1)
     (implies
      (equal (len addr1) (len addr))
      (ppp-all-poke-results-p addr addr1 value start len)))))

(defun
    ntp4vc-pearl-bitwalker-bitwalker-pokethenpeekqtvc-statement
    (addr len start value)
  (implies
   (and
    (ppp-byte-list-p addr)
    (ppp-bv32-p len)
    (ppp-bv32-p start)
    (ppp-bv64-p value)
    (< (* 8 (len addr)) 4294967296)
    (<= 0 len)
    (< len 64)
    (<= (+ start len) (* 8 (len addr)))
    (< value (ppp-maxvalue len)))
   (and
    (< len 64)
    (< (+ start len) 4294967296)
    (< (* 8 (len addr)) 4294967296)
    (ppp-all-updated-streams-p addr value start len))))

(value-triple :itpeval-statement-checked)
:q
