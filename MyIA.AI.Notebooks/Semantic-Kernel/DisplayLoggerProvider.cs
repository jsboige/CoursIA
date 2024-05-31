using Microsoft.Extensions.Logging;

namespace MyIA.AI.Notebooks;

public class DisplayLoggerProvider : ILoggerProvider
{
	private readonly LogLevel _logLevel;

	public DisplayLoggerProvider(LogLevel logLevel)
	{
		_logLevel = logLevel;
	}

	public ILogger CreateLogger(string categoryName)
	{
		return new DisplayLogger(categoryName, _logLevel);
	}

	public void Dispose() { }
}