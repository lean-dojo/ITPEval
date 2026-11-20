(in-package "ACL2")
(include-book "std/lists/append" :dir :system)

(defun my-id (x) x)
(defun guarded-id (x)
  (declare (xargs :guard t :verify-guards t))
  x)
(defthm my-id-id (equal (my-id x) x))
