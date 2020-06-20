package nl.ou.im9906;

/**
 * An exception to be thrown when a class definition is not found, typically after
 * a failed attempt to find a class in the list resulting from a call to the method
 * {@link Class#getDeclaredClasses()}
 */
public class NoSuchClassException extends ReflectiveOperationException {

    NoSuchClassException(String msg) {
        super(msg);
    }

}
