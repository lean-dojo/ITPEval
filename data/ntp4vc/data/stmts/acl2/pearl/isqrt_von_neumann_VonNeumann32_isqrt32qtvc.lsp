;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/isqrt_von_neumann_VonNeumann32_isqrt32qtvc: the 32-bit unsigned
;; integer-square-root loop verification condition, including its modular
;; arithmetic, bitwise updates, and loop-state invariant. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^32 are in bijection with the source's 32-bit words.

(defun isqrt32qtvc-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; These total functions agree with the source unsigned 32-bit operations on
;; source-typed inputs. Arithmetic and left shift are reduced modulo 2^32.

(defun isqrt32qtvc-u32 (value)
  (mod (ifix value) 4294967296))

(defun isqrt32qtvc-add (left right)
  (isqrt32qtvc-u32
   (+ (ifix left) (ifix right))))

(defun isqrt32qtvc-sub (left right)
  (isqrt32qtvc-u32
   (- (ifix left) (ifix right))))

(defun isqrt32qtvc-mul (left right)
  (isqrt32qtvc-u32
   (* (ifix left) (ifix right))))

(defun isqrt32qtvc-and (left right)
  (isqrt32qtvc-u32
   (logand (ifix left) (ifix right))))

(defun isqrt32qtvc-or (left right)
  (isqrt32qtvc-u32
   (logior (ifix left) (ifix right))))

(defun isqrt32qtvc-shift-left (value amount)
  (isqrt32qtvc-u32
   (ash (ifix value) (nfix amount))))

(defun isqrt32qtvc-shift-right (value amount)
  (isqrt32qtvc-u32
   (ash (isqrt32qtvc-u32 value)
        (- (nfix amount)))))

(defun isqrt32qtvc-sqr (value)
  (isqrt32qtvc-mul value value))

(defun isqrt32qtvc-shifted-one (amount)
  (isqrt32qtvc-shift-left 1 amount))

;; This is the source expression
;;   if m = 0 then 0 else 1 << (m - 1)
;; with both subtraction and shift interpreted as 32-bit word operations.

(defun isqrt32qtvc-half-bit (m)
  (if (equal m 0)
      0
    (isqrt32qtvc-shifted-one
     (isqrt32qtvc-sub m 1))))

(defun isqrt32qtvc-is-pow2-p (value amount)
  (equal
   (isqrt32qtvc-and
    value
    (isqrt32qtvc-sub
     (isqrt32qtvc-shifted-one amount)
     1))
   0))

;; The first four conjuncts are shared by both branches of the inner test.

(defun isqrt32qtvc-common-inner-p (m)
  (let* ((m-minus-one
          (isqrt32qtvc-sub m 1))
         (half-bit
          (isqrt32qtvc-half-bit m))
         (half-square
          (isqrt32qtvc-sqr half-bit)))
    (and
     (< (isqrt32qtvc-shift-right half-square 2)
        half-square)
     (<= m-minus-one 16)
     (equal
      (isqrt32qtvc-shift-right half-bit 1)
      (isqrt32qtvc-half-bit m-minus-one))
     (equal
      (isqrt32qtvc-shift-right half-square 2)
      (isqrt32qtvc-sqr
       (isqrt32qtvc-shift-right half-bit 1))))))

;; Consequent when the trial subtraction num >= b succeeds.

(defun isqrt32qtvc-subtraction-accepted-p
    (x res-g m num b)
  (let* ((m-minus-one
          (isqrt32qtvc-sub m 1))
         (half-bit
          (isqrt32qtvc-half-bit m))
         (half-square
          (isqrt32qtvc-sqr half-bit))
         (next-res
          (isqrt32qtvc-add res-g half-bit))
         (next-num
          (isqrt32qtvc-sub num b))
         (next-step
          (isqrt32qtvc-shifted-one m-minus-one))
         (next-bound
          (isqrt32qtvc-add next-res next-step)))
    (and
     (isqrt32qtvc-common-inner-p m)
     (isqrt32qtvc-is-pow2-p next-res m-minus-one)
     (< next-res 65536)
     (equal
      (isqrt32qtvc-or
       (isqrt32qtvc-shift-right
        (isqrt32qtvc-mul
         res-g
         (isqrt32qtvc-shifted-one m))
        1)
       half-square)
      (isqrt32qtvc-mul next-res next-step))
     (<= next-num x)
     (equal
      (isqrt32qtvc-sub x next-num)
      (isqrt32qtvc-sqr next-res))
     (<= next-bound 65536)
     (<= x
         (isqrt32qtvc-sub
          (isqrt32qtvc-sqr next-bound)
          1)))))

;; Consequent when the trial subtraction num >= b fails.

(defun isqrt32qtvc-subtraction-rejected-p
    (x res-g m num)
  (let* ((m-minus-one
          (isqrt32qtvc-sub m 1))
         (next-step
          (isqrt32qtvc-shifted-one m-minus-one))
         (next-bound
          (isqrt32qtvc-add res-g next-step)))
    (and
     (isqrt32qtvc-common-inner-p m)
     (isqrt32qtvc-is-pow2-p res-g m-minus-one)
     (< res-g 65536)
     (equal
      (isqrt32qtvc-shift-right
       (isqrt32qtvc-mul
        res-g
        (isqrt32qtvc-shifted-one m))
       1)
      (isqrt32qtvc-mul res-g next-step))
     (<= num x)
     (equal
      (isqrt32qtvc-sub x num)
      (isqrt32qtvc-sqr res-g))
     (<= next-bound 65536)
     (<= x
         (isqrt32qtvc-sub
          (isqrt32qtvc-sqr next-bound)
          1)))))

;; This preserves both nested source conditionals, including the bitwise
;; definition of b in the nonzero-half-square branch.

(defun isqrt32qtvc-loop-step-p (x res-g m num)
  (let* ((half-bit
          (isqrt32qtvc-half-bit m))
         (half-square
          (isqrt32qtvc-sqr half-bit))
         (scaled-res
          (isqrt32qtvc-mul
           res-g
           (isqrt32qtvc-shifted-one m))))
    (if (not (equal half-square 0))
        (let ((b
               (isqrt32qtvc-or
                scaled-res
                half-square)))
          (if (<= b num)
              (isqrt32qtvc-subtraction-accepted-p
               x res-g m num b)
            (isqrt32qtvc-subtraction-rejected-p
             x res-g m num)))
      (and
       (<= (isqrt32qtvc-sqr scaled-res)
           x)
       (<= x
           (isqrt32qtvc-sub
            (isqrt32qtvc-sqr
             (isqrt32qtvc-add scaled-res 1))
            1))))))

;; Preserve the source universal quantifiers over every 32-bit loop state.

(defun-sk isqrt32qtvc-all-loop-states-p (x)
  (forall (res-g m num)
    (implies
     (and
      (isqrt32qtvc-bv32-p res-g)
      (isqrt32qtvc-bv32-p m)
      (isqrt32qtvc-bv32-p num))
     (implies
      (and
       (<= m 16)
       (isqrt32qtvc-is-pow2-p res-g m)
       (< res-g 65536)
       (<= num x)
       (equal
        (isqrt32qtvc-sub x num)
        (isqrt32qtvc-sqr res-g))
       (<= (isqrt32qtvc-add
            res-g
            (isqrt32qtvc-shifted-one m))
           65536)
       (<= x
           (isqrt32qtvc-sub
            (isqrt32qtvc-sqr
             (isqrt32qtvc-add
              res-g
              (isqrt32qtvc-shifted-one m)))
            1)))
      (isqrt32qtvc-loop-step-p
       x res-g m num)))))

(defun
    ntp4vc-pearl-isqrt-von-neumann-vonneumann32-isqrt32qtvc-statement
    (x)
  (implies
   (isqrt32qtvc-bv32-p x)
   (and
    (<= 16 16)
    (equal
     32768
     (isqrt32qtvc-half-bit 16))
    (equal
     1073741824
     (isqrt32qtvc-sqr 32768))
    (isqrt32qtvc-is-pow2-p 0 16)
    (< 0 65536)
    (equal
     0
     (isqrt32qtvc-mul
      0
      (isqrt32qtvc-shifted-one 16)))
    (<= x x)
    (equal
     (isqrt32qtvc-sub x x)
     (isqrt32qtvc-sqr 0))
    (<= (isqrt32qtvc-add
         0
         (isqrt32qtvc-shifted-one 16))
        65536)
    (<= x
        (isqrt32qtvc-sub
         (isqrt32qtvc-sqr
          (isqrt32qtvc-add
           0
           (isqrt32qtvc-shifted-one 16)))
         1))
    (isqrt32qtvc-all-loop-states-p x))))

(value-triple :itpeval-statement-checked)
:q
