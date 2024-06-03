using Microsoft.Extensions.Logging;

namespace MyIA.AI.Notebooks;

public class DisplayLogger : ILogger, ILoggerFactory
{
	private readonly string _categoryName;
	private readonly LogLevel _logLevel;

	public DisplayLogger(string categoryName, LogLevel logLevel)
	{
		_categoryName = categoryName;
		_logLevel = logLevel;
	}

	public IDisposable? BeginScope<TState>(TState state ) where TState : notnull => this;

	public bool IsEnabled(LogLevel logLevel) => logLevel >= _logLevel;

	public void Log<TState>(LogLevel logLevel, EventId eventId, TState state, Exception? exception, Func<TState, Exception, string> formatter)
	{
		if (!IsEnabled(logLevel))
		{
			return;
		}
		var logEntry = $"[{logLevel}] {_categoryName} - {formatter(state, exception)}";

		if (exception != null)
		{
			
			logEntry += Environment.NewLine + exception;
			
		}

		Console.WriteLine(logEntry);

	}

	public void Dispose() { }

	public ILogger CreateLogger(string categoryName) => this;

	public void AddProvider(ILoggerProvider provider) => throw new NotSupportedException();
}