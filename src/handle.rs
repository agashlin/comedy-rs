// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your option.
// All files in the project carrying such notice may not be copied, modified, or distributed
// except according to those terms.

//! Wrapping and automatically closing handles.

use winapi::shared::minwindef::DWORD;
use winapi::shared::ntdef::NULL;
use winapi::um::errhandlingapi::GetLastError;
use winapi::um::handleapi::{CloseHandle, INVALID_HANDLE_VALUE};
use winapi::um::winnt::HANDLE;

/// Check and automatically close a Windows `HANDLE`.
#[repr(transparent)]
#[derive(Debug)]
pub struct Handle(HANDLE);

impl Handle {
    /// Take ownership of a `HANDLE`, which will be closed with `CloseHandle` upon drop.
    /// Checks for `INVALID_HANDLE_VALUE` but not `NULL`.
    ///
    /// # Safety
    ///
    /// `h` should be the only copy of the handle. `GetLastError()` is called to
    /// return an error, so the last Windows API called on this thread should have been
    /// what produced the invalid handle.
    pub unsafe fn from_valid(h: HANDLE) -> Result<Handle, DWORD> {
        if h == INVALID_HANDLE_VALUE {
            Err(GetLastError())
        } else {
            Ok(Handle(h))
        }
    }

    /// Take ownership of a `HANDLE`, which will be closed with `CloseHandle` upon drop.
    /// Checks for `NULL` but not `INVALID_HANDLE_VALUE`.
    ///
    /// # Safety
    ///
    /// `h` should be the only copy of the handle. `GetLastError()` is called to
    /// return an error, so the last Windows API called on this thread should have been
    /// what produced the invalid handle.
    pub unsafe fn from_nonnull(h: HANDLE) -> Result<Handle, DWORD> {
        if h == NULL {
            Err(GetLastError())
        } else {
            Ok(Handle(h))
        }
    }

    /// Obtains the raw `HANDLE` without transferring ownership.
    /// Do __not__ close this handle because it is still owned by the `Handle`.
    /// Do __not__ use this handle beyond the lifetime of the `Handle`.
    pub fn as_raw(&self) -> HANDLE {
        self.0
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        unsafe {
            CloseHandle(self.0);
        }
    }
}

/// Call a function that returns a `HANDLE` (`INVALID_HANDLE_VALUE` on failure), wrap result.
///
/// The handle is wrapped in a [`Handle`](handle/struct.Handle.html) which will automatically call
/// `CloseHandle()` on it. If the function fails, the error is retrieved via `GetLastError()` and
/// augmented with the name of the function and the file and line number of the macro usage.
///
/// # Example
///
/// ```ignore
/// unsafe {
///     let handle = call_valid_handle_getter!(
///         FindFirstFileA(std::ptr::null_mut(), std::ptr::null_mut())
///     )?;
/// }
/// ```
#[macro_export]
macro_rules! call_valid_handle_getter {
    ($f:ident ( $($arg:expr),* )) => {
        {
            use $crate::error::{Error, ErrorCode, FileLine, ResultExt};
            $crate::handle::Handle::from_valid($f($($arg),*))
                .map_err(|last_error| Win32Error {
                    code: last_error,
                    function: Some(stringify!($f)),
                    file_line: Some(FileLine(file!(), line!())),
                })
        }
    };

    // support for trailing comma in argument list
    ($f:ident ( $($arg:expr),+ , )) => {
        $crate::call_valid_handle_getter!($f($($arg),*))
    };
}

/// Call a function that returns a `HANDLE` (`NULL` on failure), wrap result.
///
/// The handle is wrapped in a [`Handle`](handle/struct.Handle.html) which will automatically call
/// `CloseHandle()` on it. If the function fails, the error is retrieved via `GetLastError()` and
/// augmented with the name of the function and the file and line number of the macro usage.
///
/// # Example
///
/// ```ignore
/// unsafe {
///     let handle = call_nonnull_handle_getter!(
///         CreateEventA(
///             std::ptr::null_mut(),
///             0, 0,
///             std::ptr::null_mut(),
///         )
///     )?;
/// }
/// ```
#[macro_export]
macro_rules! call_nonnull_handle_getter {
    ($f:ident ( $($arg:expr),* )) => {
        {
            use $crate::error::{Error, ErrorCode, FileLine, ResultExt};
            $crate::handle::Handle::from_nonnull($f($($arg),*))
                .map_err(|last_error| Win32Error {
                    code: last_error,
                    function: Some(stringify!($f)),
                    file_line: Some(FileLine(file!(), line!())),
                })
        }
    };

    // support for trailing comma in argument list
    ($f:ident ( $($arg:expr),+ , )) => {
        $crate::call_nonnull_handle_getter!($f($($arg),*))
    };
}
