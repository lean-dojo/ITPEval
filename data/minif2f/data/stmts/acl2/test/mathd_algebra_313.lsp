;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_313:
;; complex numbers satisfying v = i*z, v = 1 + I, and z = 2 - I have
;; i = 1/5 + (3/5)*I. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-313-statement (v i z)
  (implies
   (and (acl2-numberp v)
        (acl2-numberp i)
        (acl2-numberp z)
        (equal v (* i z))
        (equal v (+ 1 #c(0 1)))
        (equal z (- 2 #c(0 1))))
   (equal i
          (+ (/ 1 5)
             (* (/ 3 5) #c(0 1))))))

(value-triple :itpeval-statement-checked)
:q
